import Kamea.Witness5

/-!
# SelfSim5 — Self-Simulation of the N=5 Coexistence Witness

The N=5 S+D+ICP witness self-simulates: there exists a compositional
evaluation function and a term t such that
  eval(App(App(t, rep(a)), rep(b))) = atom(dot(a, b))
for all a, b ∈ Fin 5.

## Key insight

The simulation term need not be the algebraic retraction element.
In the N=5 witness, sec=ret=2 (identity on core), so the same element
serves as both section and retraction. The simulation term is atom(3)
— algebraically a *classifier*, but term-algebraically the lazy lookup
trigger. The self-simulation definition only requires ∃ eval t, so the
choice of simulation term is unconstrained by algebraic role.

## Evaluation strategy (identical structure to SelfSim6)

- atom(2) is lazy: preserves s-depth encoding structure
- atom(3) is lazy: wraps argument on first application
- App(atom(3), inner) in function position: triggers row lookup
  via s-depth decoding of inner and the argument
- All other atoms ground-reduce via the Cayley table

## Self-simulation term

t = atom(3). Despite being a classifier in the algebra, element 3
serves as the universal lookup program in the term algebra:

  Step 1: eval(App(atom(3), rep(a))) = App(atom(3), rep(a))
          (atom(3) is lazy — preserves argument)

  Step 2: eval(App(App(atom(3), rep(a)), rep(b)))
        = atom(dot(decode(rep(a)), decode(rep(b))))
        = atom(dot(a, b))
          (App(atom(3), inner) triggers row lookup via s-depth)
-/

set_option autoImplicit false

namespace SelfSim5

open KripkeWall

-- ═══════════════════════════════════════════════════════════════════
-- Term algebra with decidable equality
-- ═══════════════════════════════════════════════════════════════════

/-- Binary tree terms over Fin 5. -/
inductive Term where
  | atom : Fin 5 → Term
  | app : Term → Term → Term
  deriving DecidableEq, BEq

-- ═══════════════════════════════════════════════════════════════════
-- S-depth decoding
-- ═══════════════════════════════════════════════════════════════════

/-- Count nested section (element 2) applications.
    For rep terms: sdepth(rep(a)) = a. -/
def sdepth : Term → Nat
  | .app (.atom a) inner => if a.val = 2 then sdepth inner + 1 else 0
  | _ => 0

/-- Decode a term to Fin 5 via s-depth.
    For rep terms: decode(rep(a)) = a. -/
def decode (t : Term) : Fin 5 :=
  ⟨sdepth t % 5, Nat.mod_lt (sdepth t) (by omega)⟩

-- ═══════════════════════════════════════════════════════════════════
-- Lazy compositional evaluation
-- ═══════════════════════════════════════════════════════════════════

/-- Combine two evaluated terms:
    - atom(2) applied to v → App(atom(2), v)  (preserve s-structure)
    - atom(3) applied to v → App(atom(3), v)  (preserve for row lookup)
    - atom(a) applied to v → atom(dot(a, decode(v)))  (ground reduce)
    - App(atom(3), inner) applied to v → atom(dot(decode(inner), decode(v)))
      (row lookup: decode the row index from inner, column from v)
    - otherwise → App(u, v)  (stuck) -/
def applyEval (u v : Term) : Term :=
  match u with
  | .atom a =>
    if a.val = 2 then .app (.atom a) v
    else if a.val = 3 then .app (.atom a) v
    else .atom (dotW5 a (decode v))
  | .app (.atom a) inner =>
    if a.val = 3 then .atom (dotW5 (decode inner) (decode v))
    else .app u v
  | _ => .app u v

/-- Compositional evaluation on terms.
    Atoms are values; applications reduce both sides then combine. -/
def eval : Term → Term
  | .atom a => .atom a
  | .app s t => applyEval (eval s) (eval t)

-- ═══════════════════════════════════════════════════════════════════
-- S-depth encoding and self-simulation term
-- ═══════════════════════════════════════════════════════════════════

/-- S-depth encoding of a natural number: repN(k) = s^k(z₁) as a term. -/
def repN : Nat → Term
  | 0 => .atom ⟨0, by omega⟩
  | n + 1 => .app (.atom ⟨2, by omega⟩) (repN n)

/-- S-depth encoding of a Fin 5 element. -/
def rep (a : Fin 5) : Term := repN a.val

/-- The self-simulation term: atom(3).
    Algebraically a classifier, but term-algebraically the lazy lookup trigger. -/
def simTerm : Term := .atom ⟨3, by omega⟩

-- ═══════════════════════════════════════════════════════════════════
-- Compositionality
-- ═══════════════════════════════════════════════════════════════════

/-- **Compositionality of eval**.

    If eval(s₁) = eval(s₂), then eval(App(s₁, u)) = eval(App(s₂, u)).

    Immediate from the definition: eval(App(s, t)) = applyEval(eval(s), eval(t)),
    so the result depends on s only through eval(s). -/
theorem eval_compositional (s₁ s₂ u : Term)
    (h : eval s₁ = eval s₂) :
    eval (.app s₁ u) = eval (.app s₂ u) := by
  simp only [eval]
  rw [h]

-- ═══════════════════════════════════════════════════════════════════
-- Main theorem: the N=5 witness self-simulates
-- ═══════════════════════════════════════════════════════════════════

/-- **The N=5 coexistence witness self-simulates**.

    For all a, b ∈ Fin(5):
      eval(App(App(atom(3), rep(a)), rep(b))) = atom(a · b)

    The classifier element 3 serves as the universal lookup program.
    The s-depth encoding via element 2 provides injective input
    representation at the term level.

    Verified for all 25 cells by kernel computation. -/
theorem witness5_self_simulates :
    ∀ a b : Fin 5,
      eval (.app (.app simTerm (rep a)) (rep b)) = .atom (dotW5 a b) := by
  native_decide

/-- The N=5 witness self-simulates: existential form.
    There exists a compositional eval and a term t such that
    eval(App(App(t, rep(a)), rep(b))) = atom(a · b) for all a, b. -/
theorem witness5_self_simulates_exists :
    ∃ (ev : Term → Term) (t : Term),
      -- Compositionality
      (∀ s₁ s₂ u : Term, ev s₁ = ev s₂ → ev (.app s₁ u) = ev (.app s₂ u)) ∧
      -- Self-simulation
      (∀ a b : Fin 5, ev (.app (.app t (rep a)) (rep b)) = .atom (dotW5 a b)) :=
  ⟨eval, simTerm, eval_compositional, witness5_self_simulates⟩

end SelfSim5
