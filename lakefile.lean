import Lake
open Lake DSL

package classifier where
  version := v!"0.1.0"

@[default_target]
lean_lib CommonMath where
  defaultFacets := #[LeanLib.sharedFacet]

@[default_target]
lean_lib RV32IMC where
  defaultFacets := #[LeanLib.sharedFacet]

@[default_target]
lean_lib EBPF where
  defaultFacets := #[LeanLib.sharedFacet]

target server pkg : System.FilePath := do
  let some commonLib := pkg.findLeanLib? `CommonMath | error "CommonMath library is missing"
  let some rv32Lib := pkg.findLeanLib? `RV32IMC | error "RV32IMC library is missing"
  let common ← commonLib.shared.fetch
  let rv32 ← rv32Lib.shared.fetch
  (common.mix rv32).mapM fun _ => do
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

@[test_driver]
script check do
  let executable ← runBuild server.fetch
  let _ ← runBuild web.fetch
  let root := (← getRootPackage).dir
  let tests ← IO.Process.spawn {cmd := "cargo", args := #["test", "--manifest-path", "tooling/Cargo.toml", "--workspace"], cwd := root}
  let result ← tests.wait
  if result != 0 then return result
  let webTests ← IO.Process.spawn {cmd := "npm", args := #["test"], cwd := root / "tooling/web"}
  let webResult ← webTests.wait
  if webResult != 0 then return webResult
  let smoke ← IO.Process.spawn {cmd := "python3", args := #["tooling/scripts/smoke.py", "--server", executable.toString, "--parent-pid", toString (← IO.Process.getPID)], cwd := root}
  smoke.wait
