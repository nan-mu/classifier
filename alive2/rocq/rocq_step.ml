module ZA = Z

open Validation

let rec positive_of_zarith n =
  if ZA.equal n ZA.one then XH
  else if ZA.testbit n 0 then XI (positive_of_zarith (ZA.shift_right n 1))
  else XO (positive_of_zarith (ZA.shift_right n 1))

let coq_z_of_bits bits =
  let two64 = ZA.shift_left ZA.one 64 in
  let two63 = ZA.shift_left ZA.one 63 in
  let m = ZA.logand bits (ZA.pred two64) in
  if ZA.equal m ZA.zero then Z0
  else if ZA.geq m two63 then Zneg (positive_of_zarith (ZA.sub two64 m))
  else Zpos (positive_of_zarith m)

let vlong_of_bits bits =
  Vlong (Int64.repr (coq_z_of_bits bits))

let rec zarith_of_positive = function
  | XH -> ZA.one
  | XO p -> ZA.shift_left (zarith_of_positive p) 1
  | XI p -> ZA.logor (ZA.shift_left (zarith_of_positive p) 1) ZA.one

let zarith_of_coq = function
  | Z0 -> ZA.zero
  | Zpos p -> zarith_of_positive p
  | Zneg p -> ZA.neg (zarith_of_positive p)

let eq_z a b =
  ZA.equal (zarith_of_coq a) (zarith_of_coq b)

let hex16 bits =
  let raw = ZA.format "%x" bits in
  let pad = 16 - String.length raw in
  if pad < 0 then raw else String.make pad '0' ^ raw

let hex_of_vlong z =
  hex16 (zarith_of_coq (Int64.unsigned z))

let int64_min_z () =
  Zneg (positive_of_zarith (ZA.shift_left ZA.one 63))

let int64_min_roundtrip () =
  let zmin = int64_min_z () in
  let stored = Int64.repr zmin in
  let bits = zarith_of_coq (Int64.unsigned stored) in
  let back = Int64.signed stored in
  let two63 = ZA.shift_left ZA.one 63 in
  ZA.equal bits two63 && eq_z back zmin

type ptr_role = Code | Stack | Ctx | Other

type obs = Bv64 of ZA.t | Undef | Ptr of ptr_role * ZA.t | Unsupported

type rocq_status = Next | Exit | Stuck | Incomplete

type step = {
  pc : int;
  pc_after : [ `Index of int | `Exit | `None ];
  status : rocq_status;
  before : obs array;
  after : obs array;
  return_value : ZA.t option;
  mem_same : bool;
  load_or_store : bool;
}

let regs = [| R0; R1; R2; R3; R4; R5; R6; R7; R8; R9 |]

let ireg_of_index = function
  | 0 -> Some R0
  | 1 -> Some R1
  | 2 -> Some R2
  | 3 -> Some R3
  | 4 -> Some R4
  | 5 -> Some R5
  | 6 -> Some R6
  | 7 -> Some R7
  | 8 -> Some R8
  | 9 -> Some R9
  | _ -> None

let obs_of_val code_b ctx_b stk_b = function
  | Vundef -> Undef
  | Vlong z -> Bv64 (zarith_of_coq (Int64.unsigned z))
  | Vptr (b, ofs) ->
      let role =
        if eq_block b code_b then Code
        else if eq_block b ctx_b then Ctx
        else if eq_block b stk_b then Stack
        else Other
      in
      Ptr (role, zarith_of_coq (Ptrofs.unsigned ofs))
  | Vint _ | Vfloat _ | Vsingle _ -> Unsupported

let project_regs rs code_b ctx_b stk_b =
  Array.init 10 (fun i ->
      obs_of_val code_b ctx_b stk_b (rs (IR regs.(i))))

let is_load_or_store = function
  | Pload _ | Pstore _ | Ploadsx _ | Pload_probe _ | Ploadsx_probe _
  | Patomic _ -> true
  | _ -> false

let z_small = function
  | Z0 -> Some 0
  | Zpos p ->
      let n = zarith_of_positive p in
      if ZA.fits_int n then Some (ZA.to_int n) else None
  | Zneg _ -> None

let bytes_of_hex hex =
  let n = String.length hex in
  if n mod 2 <> 0 then failwith "odd hex length";
  let out = Array.make (n / 2) 0 in
  for i = 0 to (n / 2) - 1 do
    out.(i) <- int_of_string ("0x" ^ String.sub hex (i * 2) 2)
  done;
  out

let words_of_bytes raw =
  if Array.length raw mod 8 <> 0 then failwith "bytecode length is not a multiple of 8";
  let n = Array.length raw / 8 in
  Array.init n (fun i ->
      let acc = ref ZA.zero in
      for b = 7 downto 0 do
        acc := ZA.add (ZA.shift_left !acc 8) (ZA.of_int raw.((i * 8) + b))
      done;
      Int64.repr (coq_z_of_bits !acc))

type machine = {
  prog : ebpf_prog;
  code_b : block;
  ctx_b : block;
  stk_b : block;
  mem : Mem.mem;
}

let boot words =
  let n = Array.length words in
  let code = Array.to_list words in
  let nbytes = if n = 0 then 1 else 8 * n in
  let (m1, code_b) = Mem.alloc Mem.empty Z0 (coq_z_of_bits (ZA.of_int nbytes)) in
  let (m2, ctx_b) = Mem.alloc m1 Z0 (coq_z_of_bits (ZA.of_int 8)) in
  let (m3, stk_b) = Mem.alloc m2 Z0 bpf_stack_size in
  let prog = {
    main_code = code;
    jump_table = (fun _ -> None);
    max_entries = Z0;
  } in
  { prog; code_b; ctx_b; stk_b; mem = m3 }

let run ~bytes ~inputs =
  let raw = bytes_of_hex bytes in
  let words = words_of_bytes raw in
  let mach = boot words in
  let rs = ref (create_initial_state mach.ctx_b mach.stk_b mach.code_b) in
  List.iter (fun (reg, bits) ->
      match ireg_of_index reg with
      | None -> failwith "input register is outside r0-r9"
      | Some ireg ->
          rs := Pregmap.set (IR ireg) (vlong_of_bits bits) !rs
    ) inputs;
  let mem = ref mach.mem in
  let fuel_left = ref (Array.length words + 1) in
  let steps = ref [] in
  let stop = ref false in
  while not !stop do
    let pc_val = !rs PC in
    decr fuel_left;
      if !fuel_left < 0 then begin
        let before = project_regs !rs mach.code_b mach.ctx_b mach.stk_b in
        let pc =
          match pc_val with
          | Vptr (b, ofs) when eq_block b mach.code_b ->
              (match z_small (Ptrofs.unsigned ofs) with Some i -> i | None -> 0)
          | _ -> 0
        in
        steps := {
          pc;
          pc_after = `None;
          status = Incomplete;
          before;
          after = before;
          return_value = None;
          mem_same = true;
          load_or_store = false;
        } :: !steps;
        stop := true
      end else
        match pc_val with
        | Vptr (b, ofs) when eq_block b mach.code_b ->
            let z = Ptrofs.unsigned ofs in
            begin match z_small z with
            | None ->
                let before = project_regs !rs mach.code_b mach.ctx_b mach.stk_b in
                steps := {
                  pc = 0; pc_after = `None; status = Stuck;
                  before; after = before; return_value = None;
                  mem_same = true; load_or_store = false;
                } :: !steps;
                stop := true
            | Some pc ->
                begin match find_instr z mach.prog.main_code with
                | None ->
                    let before = project_regs !rs mach.code_b mach.ctx_b mach.stk_b in
                    steps := {
                      pc; pc_after = `None; status = Stuck;
                      before; after = before; return_value = None;
                      mem_same = true; load_or_store = false;
                    } :: !steps;
                    stop := true
                | Some insn ->
                    let before = project_regs !rs mach.code_b mach.ctx_b mach.stk_b in
                    let mem_op = is_load_or_store insn in
                    let outcome =
                      exec_instr mach.prog insn !rs [] None O !mem []
                    in
                    match outcome with
                    | Stuck ->
                        steps := {
                          pc; pc_after = `None; status = Stuck;
                          before; after = before; return_value = None;
                          mem_same = true; load_or_store = mem_op;
                        } :: !steps;
                        stop := true
                    | Next (rs', _, _, _, m') ->
                        let same = m' == !mem in
                        mem := m';
                        rs := rs';
                        let after = project_regs rs' mach.code_b mach.ctx_b mach.stk_b in
                        let next_pc = rs' PC in
                        if Val.eq next_pc vnullptr then
                          let ret = match after.(0) with
                            | Bv64 z -> Some z
                            | _ -> None
                          in
                          steps := {
                            pc; pc_after = `Exit; status = Exit;
                            before; after; return_value = ret;
                            mem_same = same; load_or_store = mem_op;
                          } :: !steps;
                          stop := true
                        else begin
                          match next_pc with
                          | Vptr (b2, ofs2) when eq_block b2 mach.code_b ->
                              begin match z_small (Ptrofs.unsigned ofs2) with
                              | Some idx ->
                                  steps := {
                                    pc; pc_after = `Index idx; status = Next;
                                    before; after; return_value = None;
                                    mem_same = same; load_or_store = mem_op;
                                  } :: !steps
                              | None ->
                                  steps := {
                                    pc; pc_after = `None; status = Stuck;
                                    before; after; return_value = None;
                                    mem_same = same; load_or_store = mem_op;
                                  } :: !steps;
                                  stop := true
                              end
                          | _ ->
                              steps := {
                                pc; pc_after = `None; status = Stuck;
                                before; after; return_value = None;
                                mem_same = same; load_or_store = mem_op;
                              } :: !steps;
                              stop := true
                        end
                end
            end
        | _ ->
            let before = project_regs !rs mach.code_b mach.ctx_b mach.stk_b in
            steps := {
              pc = 0; pc_after = `None; status = Stuck;
              before; after = before; return_value = None;
              mem_same = true; load_or_store = false;
            } :: !steps;
            stop := true
  done;
  List.rev !steps

let memory_empty steps =
  (* The first DIV64 run kept this check: exec_alu returned the same mem
     object it was given. A different object is a memory effect. *)
  List.for_all (fun s -> s.mem_same) steps

let string_of_status = function
  | Next -> "NEXT"
  | Exit -> "EXIT"
  | Stuck -> "STUCK"
  | Incomplete -> "INCOMPLETE"

let string_of_role = function
  | Code -> "code"
  | Stack -> "stack"
  | Ctx -> "ctx"
  | Other -> "other"

let print_obs oc i obs =
  Printf.fprintf oc "r%d " i;
  match obs with
  | Undef -> output_string oc "UNDEF\n"
  | Unsupported -> output_string oc "UNSUPPORTED\n"
  | Bv64 z -> Printf.fprintf oc "BV64 %s\n" (hex16 z)
  | Ptr (role, ofs) ->
      Printf.fprintf oc "PTR %s %s\n" (string_of_role role) (hex16 ofs)

let print_stream oc steps =
  output_string oc "contract NEXT EXIT STUCK INCOMPLETE\n";
  output_string oc (if memory_empty steps then "memory empty\n" else "memory changed\n");
  List.iter (fun s ->
      output_string oc "step\n";
      Printf.fprintf oc "pc %d\n" s.pc;
      Printf.fprintf oc "status %s\n" (string_of_status s.status);
      begin match s.pc_after with
      | `Index n -> Printf.fprintf oc "pc_after %d\n" n
      | `Exit -> output_string oc "pc_after exit\n"
      | `None -> output_string oc "pc_after none\n"
      end;
      begin match s.return_value with
      | None -> output_string oc "return none\n"
      | Some z -> Printf.fprintf oc "return %s\n" (hex16 z)
      end;
      output_string oc "before\n";
      Array.iteri (print_obs oc) s.before;
      output_string oc "after\n";
      Array.iteri (print_obs oc) s.after;
      output_string oc "endstep\n"
    ) steps;
  output_string oc "end\n"

let read_stdin () =
  let lines = ref [] in
  begin try
    while true do
      lines := input_line stdin :: !lines
    done
  with End_of_file -> ()
  end;
  let lines = List.rev !lines in
  let bytes = ref None in
  let inputs = ref [] in
  List.iter (fun line ->
      match String.split_on_char ' ' line with
      | ["bytes"; hex] -> bytes := Some hex
      | ["in"; reg; hex] ->
          inputs := (int_of_string reg, ZA.of_string ("0x" ^ hex)) :: !inputs
      | [""] -> ()
      | _ -> failwith ("bad request line: " ^ line)
    ) lines;
  match !bytes with
  | None -> failwith "missing bytes"
  | Some hex -> (hex, List.rev !inputs)

let prove_case name bytes inputs expect =
  let steps = run ~bytes ~inputs in
  let exit_step =
    List.find_opt (fun s -> s.status = Exit) steps
  in
  let got = match exit_step with
    | Some s -> s.return_value
    | None -> None
  in
  let got_hex = match got with
    | Some z -> hex16 z
    | None -> "none"
  in
  let mem_same = List.for_all (fun s -> s.mem_same) steps in
  let div_same =
    match List.find_opt (fun s -> s.pc = 1 && s.status = Next) steps with
    | Some s -> s.mem_same
    | None -> false
  in
  let ok = got_hex = expect && exit_step <> None in
  Printf.printf "%s exit=%s r0=%s mem_physical=%s div_mem_physical=%s\n"
    name
    (match exit_step with Some s -> string_of_status s.status | None -> "MISSING")
    got_hex
    (if mem_same then "same" else "changed")
    (if div_same then "same" else "changed");
  ok

let prove () =
  let zmin = int64_min_z () in
  let stored = Int64.repr zmin in
  let bits = hex_of_vlong stored in
  let round = int64_min_roundtrip () in
  Printf.printf "int64_min_bits=%s\n" bits;
  Printf.printf "int64_min_roundtrip=%s\n" (if round then "ok" else "FAIL");
  let div = "bf100000000000003f200000000000009500000000000000" in
  let a = prove_case "div64-7-2" div [(1, ZA.of_int 7); (2, ZA.of_int 2)]
      "0000000000000003" in
  let b = prove_case "div64-7-0" div [(1, ZA.of_int 7); (2, ZA.of_int 0)]
      "0000000000000000" in
  if not (round && a && b) then exit 1

let () =
  match Array.to_list Sys.argv with
  | [_; "--prove"] -> prove ()
  | [_; "--contract"] ->
      print_endline "contract NEXT EXIT STUCK INCOMPLETE";
      print_endline "end"
  | [_] ->
      let bytes, inputs = read_stdin () in
      let steps = run ~bytes ~inputs in
      print_stream stdout steps
  | _ ->
      prerr_endline "usage: rocq-step [--prove|--contract]";
      exit 2
