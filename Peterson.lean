/-! # Peterson's algorithm
https://en.wikipedia.org/wiki/Peterson%27s_algorithm

Two processes share three variables: `flag[0]`, `flag[1]`, and `turn`.
`flag[i] = true` means "process `i` wants to enter the critical section".
`turn` decides who goes first when both want to enter.

Each process runs the program below. The label on the left is the value of the
process's program counter (`PC`). The name on the right is the transition (`Step`
constructor) that executes that line. Each line is one atomic step.

Process 0:
idle:      flag[0] := true;                -- raise
trying:    turn := 1;                      -- yield
waiting:   if !flag[1] then goto critical  -- flagDown
           else goto checking              -- flagUp
checking:  if turn = 0 then goto critical  -- myTurn
           else goto waiting               -- notMyTurn
critical:  <do something critical>         -- exclusive
finishing: flag[0] := false                -- exit
           goto idle

Process 1 (same program, with 0 and 1 swapped):
idle:      flag[1] := true;                -- raise
trying:    turn := 0;                      -- yield
waiting:   if !flag[0] then goto critical  -- flagDown
           else goto checking              -- flagUp
checking:  if turn = 1 then goto critical  -- myTurn
           else goto waiting               -- notMyTurn
critical:  <do something critical>         -- exclusive
finishing: flag[1] := false                -- exit
           goto idle

Wikipedia writes the entry loop as `while (flag[1] && turn == 1) {}`.
We split it into two separate reads (`waiting` reads the flag, `checking` reads `turn`).
This allows more interleavings than the textbook version, so our safety proof
covers more behaviors.
-/
namespace Peterson

attribute [grind =] Vector.getElem_mk

/-- The program counter: the line each process is about to execute. -/
inductive PC where
  | idle
  | trying
  | waiting
  | checking
  | critical
  | finishing
  deriving DecidableEq

/-- Process identifiers: `0` and `1`. We use `abbrev` so that Lean sees through it
and reuses everything it knows about `Fin 2` (numerals, `decide`, ...). -/
abbrev PId := Fin 2

/-- The other process. The `@[grind]` attribute lets `grind` use its equations. -/
@[local grind]
def PId.other : PId → PId
  | 0 => 1
  | 1 => 0

example (pid : PId) : pid.other ≠ pid := by
  grind

example (pid : PId) : pid.other.other = pid := by
  grind

/-- A process identifier is `0` or `1`. `grind` reasons about `pid` symbolically,
and does not know *yet* that `Fin 2` has only two values. This theorem tells it.
`@[grind]` uses the pattern `p.val`, so whenever `↑pid` appears in a goal,
`grind` adds this disjunction and splits on it. -/
@[local grind] theorem PId.val_cases (p : PId) : p.val = 0 ∨ p.val = 1 := by lia

/-- The global state: the program counter of each process, plus the shared variables. -/
structure State where
  pc   : Vector PC 2
  flag : Vector Bool 2
  turn : PId

/-- Initial state: both processes idle, no flag raised. -/
@[local grind]
def init : State :=
  { pc   := #v[.idle, .idle]
    flag := #v[false, false]
    turn := 0 }

/-!
## Transitions

`Step s t` means "the system can move from state `s` to state `t` in one step".
There is one constructor per line of the program. Each constructor says:
if process `pid` is at a given line (and the guard holds), then `pid` executes
that line. The other process does not move.

`{ s with pc := ... }` is the state `s` with only the listed fields changed.
-/
inductive Step : State → State → Prop where
  /- idle:  flag[pid] := true; -/
  | raise (s : State) (pid : PId) :
    s.pc[pid] = .idle →
    Step s { s with pc   := s.pc.set pid .trying
                    flag := s.flag.set pid true }
  /- trying: turn := pid.other; -/
  | yield (s : State) (pid : PId) :
    s.pc[pid] = .trying →
    Step s { s with pc   := s.pc.set pid .waiting
                    turn := pid.other }
  /- waiting:
     if !flag[pid.other] then goto critical  -- flagDown
     else goto checking                      -- flagUp
  -/
  | flagDown (s : State) (pid : PId) :
    s.pc[pid] = .waiting →
    s.flag[pid.other] = false →
    Step s { s with pc := s.pc.set pid .critical }
  | flagUp (s : State) (pid : PId) :
    s.pc[pid] = .waiting →
    s.flag[pid.other] = true →
    Step s { s with pc := s.pc.set pid .checking }
  /- checking:
     if turn = 0 then goto critical  -- myTurn
     else goto waiting               -- notMyTurn
  -/
  | myTurn (s : State) (pid : PId) :
    s.pc[pid] = .checking →
    s.turn = pid →
    Step s { s with pc := s.pc.set pid .critical }
  | notMyTurn (s : State) (pid : PId) :
    s.pc[pid] = .checking →
    s.turn ≠ pid →
    Step s { s with pc := s.pc.set pid .waiting }
  /- critical: <do something critical> -/
  | exclusive (s : State) (pid : PId) :
    s.pc[pid] = .critical →
    Step s { s with pc := s.pc.set pid .finishing }
  /-
    flag[pid] := false;
    goto idle;
  -/
  | exit (s : State) (pid : PId) :
    s.pc[pid] = .finishing →
    Step s { s with pc   := s.pc.set pid .idle
                    flag := s.flag.set pid false }

def Deterministic (R : α → α → Prop) : Prop :=
  ∀ s₁ s₂ s₃, R s₁ s₂ → R s₁ s₃ → s₂ = s₃

/-- `Step` is a relation, not a function: a state can have several successors.
From `init`, either process can move first. This nondeterminism models the
scheduler, which may run the processes in any order. -/
theorem step_not_det : ¬ Deterministic Step := by
  intro h
  let s₁ := init
  let s₂ : State := { pc   := #v[.trying, .idle]
                      flag := #v[true, false]
                      turn := 0 }
  let s₃ : State := { pc   := #v[.idle, .trying]
                      flag := #v[false, true]
                      turn := 0 }
  replace h := h s₁ s₂ s₃
  replace h := h (.raise s₁ 0 rfl)
  replace h := h (.raise s₁ 1 rfl)
  simp [s₂, s₃] at h

/-- The states the system can reach from `init` in zero or more steps. -/
inductive Reachable : State → Prop where
  | init : Reachable init
  | step : (s₁ s₂ : State) → Reachable s₁ → Step s₁ s₂ → Reachable s₂

/-- The main proof principle. To show that `P` holds in every reachable state,
show that `P` holds initially (`h₀`) and that every step preserves it (`h₁`).
A property with these two properties is called an *inductive invariant*. -/
theorem induction (P : State → Prop)
    (h₀ : P init)
    (h₁ : ∀ s t, P s → Step s t → P t) :
    ∀ s, Reachable s → P s := by
  intro s h
  induction h <;> grind

/-!
## Mutual exclusion

We want to prove that the two processes are never in the critical section at
the same time.
-/

/-- Mutual exclusion: the two processes are never both in the critical section. -/
@[local grind]
def Safe (s : State) : Prop :=
  ¬ (s.pc[0] = .critical ∧ s.pc[1] = .critical)

/-!
`Safe` is not an inductive invariant by itself. Consider the state
`pc = [critical, checking]`, `flag = [true, true]`, `turn = 1`.
It is `Safe`, but process 1 can take `myTurn` and enter the critical section.
This state is not reachable, but `induction` does not know that: `h₁` must hold
for *every* state that satisfies `P`.

So we prove a stronger property, `Inv`, that rules out such states.
Finding the right invariant is the creative part of the proof.
Checking it is routine, and `grind` does it for us.
-/

/-- `flag[i]` is raised exactly when process `i` is outside `idle`. -/
@[local grind]
def FlagInv (s : State) (i : PId) : Prop :=
  s.flag[i] = true ↔ s.pc[i] ≠ .idle

/-- If `i` is in the critical section and the other process already yielded,
then the turn belongs to `i`.

The `.critical` case is what gives mutual exclusion: if both processes were
critical, `TurnInv s 0` and `TurnInv s 1` would give `turn = 0` and `turn = 1`. -/
@[local grind]
def TurnInv (s : State) (i : PId) : Prop :=
  s.pc[i] = .critical →
  (s.pc[i.other] = .waiting ∨ s.pc[i.other] = .checking ∨ s.pc[i.other] = .critical) →
  s.turn = i

/-- The inductive invariant: `FlagInv` and `TurnInv` for both processes. -/
@[local grind]
def Inv (s : State) : Prop :=
  FlagInv s 0 ∧ FlagInv s 1 ∧ TurnInv s 0 ∧ TurnInv s 1

/-- `Inv` holds initially. `init` is a concrete state, so `decide` can just check it. -/
theorem inv_init : Inv init := by
  grind

/-- Every step preserves `Inv`. We split on which transition was taken and which
process took it. With a concrete process (`0` or `1`), `grind` can compute
`pid.other` and the updated vectors, and finish each case. -/
theorem inv_step {s t : State} : Inv s → Step s t → Inv t := by
  intro h hs
  cases hs <;> grind

/-- `Inv` is stronger than `Safe`. -/
theorem inv_safe {s : State} : Inv s → Safe s := by
  grind

/-- Mutual exclusion holds in every reachable state:
`Inv` is an inductive invariant, and it implies `Safe`. -/
theorem safety : ∀ s, Reachable s → Safe s := fun s h =>
  inv_safe (induction Inv inv_init (fun _ _ => inv_step) s h)

/-- The state from the comment above is not reachable: it violates `TurnInv s 0`.
Process 0 is critical and process 1 is `checking`, so `Inv` demands `turn = 0`,
but `turn = 1`. Every reachable state satisfies `Inv`, so this one is not reachable. -/
example : ¬ Reachable { pc := #v[.critical, .checking], flag := #v[true, true], turn := 1 } := by
  intro h
  have := induction Inv inv_init (fun _ _ => inv_step) _ h
  grind

/-
`e |>.f args` means `(e).f args`
-/
#eval [3, 1, 2] |>.map (· * 10) |>.reverse                -- [20, 10, 30]
#eval ([3, 1, 2].map (· * 10)).reverse                    -- [20, 10, 30]
#eval ([3, 1, 2].map (fun x => x * 10)).reverse           -- [20, 10, 30]
#eval List.reverse ([3, 1, 2].map (fun x => x * 10))      -- [20, 10, 30]
#eval List.reverse (List.map (fun x => x * 10) [3, 1, 2]) -- [20, 10, 30]


/-- Sanity check: process 0 can enter the critical section, so `safety` is not vacuous.
If a bug in `Step` made `critical` unreachable, `safety` would still be provable!
This example protects us against that mistake. -/
example : ∃ s, Reachable s ∧ s.pc[0] = .critical :=
  ⟨_, Reachable.init
      |>.step _ _ (.raise _ 0 rfl)
      |>.step _ _ (.yield _ 0 rfl)
      |>.step _ _ (.flagDown _ 0 rfl rfl),
   rfl⟩

/-!
## Executing the algorithm

`Step` is a relation, so we cannot run it. But once we choose *which* process
moves, the next state is fully determined. `next s pid` computes it.
-/

/-- The state after process `pid` executes its current line. -/
def next (s : State) (pid : PId) : State :=
  match s.pc[pid] with
  | .idle => { s with pc := s.pc.set pid .trying, flag := s.flag.set pid true }
  | .trying => { s with pc := s.pc.set pid .waiting, turn := pid.other }
  | .waiting =>
    if s.flag[pid.other] = false then
      { s with pc := s.pc.set pid .critical }
    else
      { s with pc := s.pc.set pid .checking }
  | .checking =>
    if s.turn = pid then
      { s with pc := s.pc.set pid .critical }
    else
      { s with pc := s.pc.set pid .waiting }
  | .critical => { s with pc := s.pc.set pid .finishing }
  | .finishing => { s with pc := s.pc.set pid .idle, flag := s.flag.set pid false }

/-- `next` agrees with `Step`: every `next` move is a valid step... -/
theorem next_sound : Step s (next s pid) := by
  grind [Step, next]

/-- ...and every step is a `next` move of some process.
Together: `Step s t ↔ ∃ pid, next s pid = t`. -/
theorem next_complete (h : Step s₁ s₂) : ∃ pid, next s₁ pid = s₂ := by
  cases h with
  | raise pid | yield pid | flagDown pid | flagUp pid
  | myTurn pid | notMyTurn pid | exclusive pid | exit pid =>
    exists pid <;> grind [next]

/-- Run a *schedule*: the list says which process moves at each step. -/
def run (s : State) : List PId → State
  | [] => s
  | p :: ps => run (next s p) ps

instance : ToString PC where
  toString pc := match pc with
    | .idle => "idle"
    | .trying => "trying"
    | .waiting => "waiting"
    | .checking => "checking"
    | .critical => "critical"
    | .finishing => "finishing"

/-- States print as `pc[0][flag[0]], pc[1][flag[1]], turn`. -/
instance : ToString State where
  toString s := s!"pc = {s.pc.toList}, flag = {s.flag.toList}, turn = {s.turn}"

#eval run init []  -- pc = [idle, idle], flag = [false, false], turn = 0

/-- Every schedule from a reachable state ends in a reachable state. -/
theorem Reachable.run (h : Reachable s) : ∀ ps, Reachable (run s ps)
  | [] => h
  | _ :: ps => Reachable.run (.step _ _ h next_sound) ps

/- Both processes compete. Process 0 yields last, so `turn = 1` and process 1 wins.
Process 0 sees `turn = 1` and goes back to `waiting`; it enters only after process 1 leaves.
Try other schedules! -/
#eval run init [0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0]  -- pc = [critical, idle], flag = [true, false], turn = 1

/-- The same schedule as a proof that process 0 can reach the critical section.
`rfl` works because Lean can compute `run` on a concrete schedule. -/
example : ∃ s, Reachable s ∧ s.pc[0] = .critical :=
  ⟨_, Reachable.init.run [0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0], rfl⟩

end Peterson
