/-
The `@[trocq]` attribute + its environment extension.

Tagging a constant `w` with `@[trocq]` records its NAME; the witness is classified (base / relator /
term-primitive) lazily by `Trocq.parseEntry` (in `Registry.lean`) from `w`'s type, at the point a
surface (`transfer%` / `trocq` / `translate%`) builds its registries. Keeping parsing out of the
attribute keeps this file dependency-free (it cannot mention `Param`, which is defined downstream).
-/
import Lean
open Lean
namespace Trocq

/-- the set of constants tagged `@[trocq]`. -/
initialize trocqExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn   := Array.push
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
  }

initialize registerBuiltinAttribute {
  name  := `trocq
  descr := "register a Trocq relatedness witness (base equivalence / relator / term primitive)"
  add   := fun decl _stx _kind => modifyEnv (trocqExt.addEntry · decl)
}

/-- the names tagged `@[trocq]` in the given environment. -/
def trocqEntries (env : Environment) : Array Name := trocqExt.getState env

end Trocq
