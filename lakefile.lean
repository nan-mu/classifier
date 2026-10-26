import Lake
open Lake DSL

package classifier where
  version := v!"0.1.0"
  srcDir := "src"

@[default_target]
lean_lib Core where
  roots := #[`Term, `Expression, `Observation, `Interface, `Wire, `Match]
  defaultFacets := #[LeanLib.sharedFacet]

@[default_target]
lean_lib Node where
  defaultFacets := #[LeanLib.sharedFacet]

@[default_target]
lean_lib RV32 where
  roots := #[`Cross.RV32, `Cross.RV32.RegisterFfi]
  defaultFacets := #[LeanLib.sharedFacet]

@[default_target]
lean_lib EBPF where
  roots := #[`Cross.EBPF]
  defaultFacets := #[LeanLib.sharedFacet]

/-- Sorry-free semantic statements. `lake build Verification`. -/
lean_lib Verification where
  roots := #[`Verification]

/-- Required obligations (`sorry`) and external-premise candidates.
Not imported by `Verification`. `lake build VerificationGaps`. -/
lean_lib VerificationGaps where
  roots := #[`Verification.Unverified.Required, `Verification.Unverified.Assumed]

target server pkg : System.FilePath := do
  let some exprLib := pkg.findLeanLib? `Core | error "Core library is missing"
  let some pathLib := pkg.findLeanLib? `Node | error "Node library is missing"
  let some rv32Lib := pkg.findLeanLib? `RV32 | error "RV32 library is missing"
  let expr ← exprLib.shared.fetch
  let path ← pathLib.shared.fetch
  let rv32 ← rv32Lib.shared.fetch
  ((expr.mix path).mix rv32).mapM fun _ => do
    let output ← IO.Process.output {cmd := "cargo", args := #["build", "--manifest-path", "tooling/Cargo.toml", "-p", "server", "--message-format=json-render-diagnostics"], cwd := pkg.dir}
    unless output.stderr.isEmpty do logInfo output.stderr
    if output.exitCode != 0 then error s!"Cargo build failed with code {output.exitCode}"
    for line in output.stdout.splitOn "\n" do
      if let .ok message := Lean.Json.parse line then
        if message.getObjValD "reason" == Lean.toJson "compiler-artifact" &&
            (message.getObjValD "target").getObjValD "name" == Lean.toJson "server" then
          if let .ok executable := (message.getObjValD "executable").getStr? then
            return System.FilePath.mk executable
    error "Cargo did not report the server executable"

target web pkg : Unit := do
  Job.async do
    proc {cmd := "npm", args := #["ci"], cwd := pkg.dir / "tooling/web"}
    proc {cmd := "npm", args := #["run", "build"], cwd := pkg.dir / "tooling/web"}

@[default_target]
target tooling : Unit := do
  let serverJob ← server.fetch
  let webJob ← web.fetch
  return (serverJob.map fun _ => ()).mix webJob

script dev do
  let executable ← runBuild server.fetch
  let root := (← getRootPackage).dir
  let setup ← IO.Process.spawn {cmd := "npm", args := #["ci"], cwd := root / "tooling/web"}
  let result ← setup.wait
  if result != 0 then return result
  let child ← IO.Process.spawn {cmd := "python3", args := #["tooling/scripts/dev.py", "--server", executable.toString, "--parent-pid", toString (← IO.Process.getPID)], cwd := root}
  child.wait

/-- Profile outcomes, the sorry-free `Verification` library, then Rust tests.
Web Vitest and the live HTTP smoke script are not part of this gate. -/
@[test_driver]
script check do
  let root := (← getRootPackage).dir
  let profile ← IO.Process.spawn {
    cmd := "cargo"
    args := #[
      "test", "--manifest-path", "tooling/Cargo.toml", "-p", "server",
      "--test", "profile_expect"
    ]
    cwd := root
  }
  let profileResult ← profile.wait
  if profileResult != 0 then return profileResult
  let pkg ← getRootPackage
  match pkg.findLeanLib? `Verification with
  | none => do
    IO.eprintln "Verification library is missing"
    return 1
  | some vlib => do
    let _ ← runBuild vlib.fetch
    let units ← IO.Process.spawn {
      cmd := "cargo"
      args := #[
        "test", "--manifest-path", "tooling/Cargo.toml", "--workspace",
        "--lib", "--bins", "--tests", "--", "--skip", "profile_programs_match_expect"
      ]
      cwd := root
    }
    units.wait
