/-
The `@[trocq]` attribute + its environment extension.

Tagging a constant `w` with `@[trocq]` classifies it immediately (via `LeTrocq.parseEntry`, reading `w`'s
type) and stores the resulting `RegKind` in the extension. So a malformed witness is rejected right at
the tag site, and the surfaces (`transfer%` / `trocq` / `translate%`) just read pre-parsed entries.
-/
import LeTrocq.Registry
open Lean Lean.Meta
namespace LeTrocq

/-- the classified `@[trocq]` witnesses (bases / relators / term primitives). -/
initialize trocqExt : SimplePersistentEnvExtension RegKind (Array RegKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

initialize registerBuiltinAttribute {
  name  := `trocq
  descr := "register a LeTrocq relatedness witness (base equivalence / relator / term primitive)"
  add   := fun decl _stx _kind => do
    let entry ← (parseEntry decl).run'
    modifyEnv (trocqExt.addEntry · entry)
}

/-- the classified witnesses registered in the given environment. -/
def trocqEntries (env : Environment) : Array RegKind := trocqExt.getState env

end LeTrocq
