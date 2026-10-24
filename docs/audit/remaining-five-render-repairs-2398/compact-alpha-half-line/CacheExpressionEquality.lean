module
import all CompactAlphaHalfLineChallenge
import all Lean.Meta.Match.Match
public import Lean
open Lean Elab Command Term
run_cmd do
 let old ← liftTermElabM <| elabTerm (← `(fun (env : Lean.Environment) => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {})) none
 let new ← liftTermElabM <| elabTerm (← `(fun (env : Lean.Environment) => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {})) none
 unless old == new do throwError "Cache-reset elaborations differ"
 IO.FS.writeFile "/home/Palomar/workspace/arithmetic-theta/evidence/remaining-four-matcher-preservation-2385/compact-alpha-half-line/cache-expression-equality.json" "{\"passed\":true,\"exact_expression_equal\":true}\n"
 logInfo "CACHE_RESET_EXACT_EXPRESSION_EQUAL"
