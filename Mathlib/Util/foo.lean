import Lean
import Mathlib.Data.ListM.DepthFirst
import Mathlib.Init.ZeroOne
import Mathlib.Data.List.Basic

open Lean Elab Tactic

structure Goals where
  active : List MVarId
  suspended : List MVarId

namespace Goals

def singleton (g : MVarId) : Goals := { active := [g], suspended := [] }

def done (G : Goals) : Bool := G.active.isEmpty

def liftTactic (t : MVarId → MetaM (List MVarId)) : Goals → MetaM Goals :=
fun G => do match G.active with
| [] => failure
| g :: gs => pure { G with active := (← t g) ++ gs }

end Goals

-- def kleisli (m : Type v → Type v) (α : Type u) (β : Type v) :=
-- α → m β

-- namespace kleisli

-- def of [Pure m] (f : α → β) : kleisli m α β := fun a => pure (f a)

-- instance [Monad m] : HAndThen (kleisli m α β) (kleisli m β γ) (kleisli m α γ) :=
--   ⟨fun f g a => f a >>= g ()⟩

-- def joinLift {n : Type v → Type v} [Monad n] [MonadLift n m] [Monad m]
--     (f : kleisli m α (n β)) : kleisli m α β :=
-- (joinM <| liftM <$> f ·)

-- instance [Alternative m] [Monad m] : MonadLift List m where
--   monadLift := fun L => L.firstM pure

-- def joinList [Alternative m] [Monad m] (f : kleisli m α (List β)) : kleisli m α β :=
-- joinLift f

-- end kleisli

-- unsafe abbrev ndFunction (α : Type) (β : Type) := kleisli (ListM MetaM) α β
unsafe abbrev ndFunction (α : Type) (β : Type) := α → ListM MetaM β

namespace ndFunction

-- unsafe def joinList (f : ndFunction α (List β)) : ndFunction α β := fun a => do (← f a).firstM pure
-- unsafe def joinMetaM (f : ndFunction α (MetaM β)) : ndFunction α β := fun a => ((f a).map .monadLift).join

-- unsafe def joinList (f : ndFunction α (List β)) : ndFunction α β := (joinM <| liftM <$> f ·)
-- unsafe def joinMetaM (f : ndFunction α (MetaM β)) : ndFunction α β := (joinM <| liftM <$> f ·)

-- unsafe instance : Coe (α → β) (ndFunction α β) := ⟨fun f a => pure (f a)⟩
-- unsafe instance : Coe (α → MetaM β) (ndFunction α β) := ⟨fun f => joinMetaM f⟩
-- unsafe instance : Coe (α → MetaM (List (MetaM β))) (ndFunction α β) := ⟨fun f => joinMetaM (joinList (joinMetaM f))⟩
-- unsafe instance : Coe (ndFunction α (List β)) (ndFunction α β) := ⟨joinList⟩
-- unsafe instance : Coe (ndFunction α (MetaM β)) (ndFunction α β) := ⟨joinMetaM⟩

-- unsafe example (f : α → β) : ndFunction α β := f
-- unsafe example (f : α → List β) : ndFunction α β := f
-- unsafe example (f : α → MetaM β) : ndFunction α β := f
-- unsafe example (f : α → MetaM (List β)) : ndFunction α β := f
-- unsafe example (f : α → MetaM (List (MetaM β))) : ndFunction α β := f


end ndFunction

-- unsafe abbrev ndTactic := ndFunction Goals Goals
unsafe abbrev ndTactic := Goals → ListM MetaM Goals

unsafe def ListM.squish (L : MetaM (List (MetaM α))) : ListM MetaM α :=
.squash do pure <| .ofListM (← L)

namespace ndTactic

unsafe def of (t : MVarId → MetaM (List (MetaM (List MVarId)))) : ndTactic :=
fun G => do match G.active with
| [] => failure
| g :: gs =>
  ListM.squish (t g) |>.map fun hs => { G with active := hs ++ gs }

unsafe instance : HOrElse ndTactic ndTactic ndTactic :=
  ⟨fun f g a => (f a).append (g () a)⟩

unsafe instance : HAndThen ndTactic ndTactic ndTactic :=
  ⟨fun f g a => f a >>= g ()⟩

/--
Move the main goal to the suspended list if it satisfies the predicate,
and otherwise do nothing.
-/
unsafe def suspend (p : MVarId → MetaM Bool) : ndTactic :=
fun G => do match G.active with
| [] => failure
| g :: gs =>
  if ← p g then
    pure { G with active := gs, suspended := g :: G.suspended }
  else
    pure G

/--
Takes a procedure which inspects the list of active goals and either
* fails, signaling no outcomes
* returns `none`, signalling the active goals should not be changed, or
* returns `some A`, signalling the active goals should be replaced with `A`.

Returns a non-deterministic tactic,
with either 0 (in the case of failure) or 1 (otherwise) outcomes.
-/
unsafe def proc (f : List MVarId → MetaM (Option (List MVarId))) : ndTactic :=
fun G => do match ← f G.active with
| none => pure G
| some A' => pure { G with active := A' }


unsafe def discharge (f : MVarId → MetaM (Option (List MVarId))) : ndTactic :=
fun G => do match G.active with
| [] => failure
| g :: gs => do match ← f g with
  | none => pure { }

/--
Given a nondeterministic tactic `t`,
construct the nondeterministic tactic which considers every possible iteration of `t`.
-/
unsafe def depthFirst (t : ndTactic) : ndTactic := depthFirst t

/--
Run a nondeterministic tactic:
find the first choice with no active goals, returning the suspended goals,
or fail.
-/
unsafe def run (t : ndTactic) : MVarId → MetaM (List MVarId) :=
fun g => (t (.singleton g) |>.filter Goals.done |>.head) <&> Goals.suspended

end ndTactic

def Lean.MVarId.nondeterministic
    (choices : MVarId → MetaM (List (MetaM (List MVarId))))
    (proc : List MVarId → MetaM (Option (List MVarId)) := fun _ => pure none)
    (suspend : MVarId → MetaM Bool := fun _ => pure false) :
    MVarId → MetaM (List MVarId) :=
unsafe fun g => ((ndTactic.proc proc >> ndTactic.suspend suspend >> ndTactic.of choices).depthFirst).run g
