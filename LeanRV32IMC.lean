import CommonMath
import LeanRV32IMC.Types
import LeanRV32IMC.Decode
import LeanRV32IMC.Value
import LeanRV32IMC.Ffi

/-!
# LeanRV32IMC — RV32IMC slice for the classifier

Split modules:
* `LeanRV32IMC.Types` — regidx / op tags / `instruction`
* `LeanRV32IMC.Decode` — encdec backwards
* `LeanRV32IMC.Value` — Expr value functions (`value` / `step`)
* `LeanRV32IMC.Ffi` — `@[export]` entry points for the Rust test crate

Shared mathematics lives in `CommonMath` (`doc/common-math.md`).
Sail execute / SailM / ExecutionResult have been removed.
-/
