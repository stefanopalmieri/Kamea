/- # SelfSimulation — Partial Application Injectivity

   ## Summary

   We prove that self-simulation in an extensional magma forces the
   partial application map to be injective. This is the first formal
   theorem connecting self-simulation to algebraic structure — Layer 0
   of the inevitability argument.

   The setup is minimal: a finite extensional magma with a binary
   operation, an evaluation function on terms satisfying compositionality
   (the result of evaluating `App(f, x)` depends on `f` only through
   `eval(f)`), and a Q-depth encoding via a distinguished element.

   ## Results

   1. **Partial application injectivity**: if a single term `t` computes
      the entire Cayley table under Q-depth encoding, then the map
      `a ↦ eval(App(t, rep(a)))` is injective.

   2. **Partial application distinctness**: distinct elements produce
      distinct intermediate terms (contrapositive of 1).

   3. **Encoding injectivity**: the Q-depth encoding `rep` must itself
      be injective (immediate corollary of 1).

   All proofs are purely algebraic — no `decide`, no `native_decide`.
   Every theorem holds for ALL magmas satisfying the axioms, regardless
   of carrier size or specific table entries.

   ## Proof idea

   If `eval(App(t, rep(a₁))) = eval(App(t, rep(a₂)))`, then by
   compositionality, `eval(App(App(t, rep(a₁)), rep(b)))` equals
   `eval(App(App(t, rep(a₂)), rep(b)))` for all `b`. By
   self-simulation, both equal `atom(dot(aᵢ, b))`, forcing
   `dot(a₁, b) = dot(a₂, b)` for all `b`. Extensionality gives
   `a₁ = a₂`.

   The information-theoretic content: a self-simulator cannot compress
   the encoding. It must maintain enough information in each partial
   application to reconstruct the full row of the corresponding element.
-/

set_option autoImplicit false

namespace SelfSimulation

-- ══════════════════════════════════════════════════════════════════════
-- Part 1: Term Algebra
-- ══════════════════════════════════════════════════════════════════════

/-- Terms over a finite carrier of size `n`: atoms (elements of `Fin n`)
    or binary applications.

    This is the free binary-tree algebra over `Fin n`. The Ψ∗ term algebra
    is an instance with `n = 16` and specific evaluation semantics. -/
inductive Term (n : Nat) where
  | atom : Fin n → Term n
  | app : Term n → Term n → Term n

/-- Atom constructor is injective: `atom a = atom b → a = b`. -/
theorem Term.atom_injective {n : Nat} {a b : Fin n}
    (h : Term.atom a = Term.atom b) : a = b := by
  cases h; rfl

-- ══════════════════════════════════════════════════════════════════════
-- Part 2: Q-Depth Encoding
-- ══════════════════════════════════════════════════════════════════════

/-- Q-depth encoding of a natural number: `repN q top k = Q^k(⊤)`.
    - `repN q top 0 = atom top`
    - `repN q top (k+1) = app (atom q) (repN q top k)` -/
def repN {n : Nat} (q top : Fin n) : Nat → Term n
  | 0 => .atom top
  | k + 1 => .app (.atom q) (repN q top k)

/-- Q-depth encoding of a finite element: `rep q top a = Q^(a.val)(⊤)`. -/
def rep {n : Nat} (q top : Fin n) (a : Fin n) : Term n :=
  repN q top a.val

-- ══════════════════════════════════════════════════════════════════════
-- Part 3: Self-Simulating Magma
-- ══════════════════════════════════════════════════════════════════════

/-- A finite extensional magma equipped with a compositional evaluation
    function and Q-depth encoding.

    This is the minimal structure for the injectivity theorem. It does
    NOT assume the Kripke dichotomy, branching, composition, or any
    operational axiom. Only extensionality (faithful left regular
    representation) and compositionality of `eval` (standard for any
    evaluation strategy that reduces the function position first). -/
structure SelfSimMagma (n : Nat) where
  /-- Binary operation (the Cayley table). -/
  dot : Fin n → Fin n → Fin n

  /-- Evaluation function on terms.
      Abstract — we axiomatize properties, not implementation. -/
  eval : Term n → Term n

  /-- Distinguished section element (Q / quote / successor). -/
  q : Fin n

  /-- Distinguished zero element (⊤ / top / base case). -/
  top : Fin n

  /-- **Extensionality**: elements with identical rows are equal.
      Equivalently, the left regular representation is faithful.
      This is a standard magma property — `FaithfulRetractMagma`
      in `CatKripkeWallMinimal.lean` assumes it. -/
  extensional : ∀ a b : Fin n,
    (∀ x : Fin n, dot a x = dot b x) → a = b

  /-- **Compositionality**: `eval` is congruent in the function position.
      If two terms evaluate to the same result, applying them to the
      same argument and evaluating gives the same result.

      This holds for any evaluation strategy that reduces the function
      position before acting on the result: call-by-value, call-by-name,
      the Ψ∗ evaluator, etc. It is the standard requirement that
      evaluation is deterministic and context-free in the function
      position. -/
  eval_comp : ∀ s₁ s₂ u : Term n,
    eval s₁ = eval s₂ → eval (.app s₁ u) = eval (.app s₂ u)

/-- **Self-simulation**: a single term `t` computes the entire Cayley
    table under Q-depth encoding.

    For all elements `a, b` in the carrier:
      `eval(App(App(t, rep(a)), rep(b))) = atom(dot(a, b))`

    One program, all inputs. This is the operational definition of
    self-description: the term algebra can compute the magma's own
    binary operation. -/
def SelfSimulates {n : Nat} (M : SelfSimMagma n) : Prop :=
  ∃ t : Term n, ∀ a b : Fin n,
    M.eval (.app (.app t (rep M.q M.top a)) (rep M.q M.top b)) =
    .atom (M.dot a b)

-- ══════════════════════════════════════════════════════════════════════
-- Part 4: Universal Theorems
-- ══════════════════════════════════════════════════════════════════════

section Theorems

variable {n : Nat} (M : SelfSimMagma n)

/-- **Partial application injectivity**: if a magma self-simulates,
    then the partial application map `a ↦ eval(App(t, rep(a)))` is
    injective.

    Proof:
    1. Assume `eval(App(t, rep(a₁))) = eval(App(t, rep(a₂)))`.
    2. By compositionality, for all `b`:
       `eval(App(App(t, rep(a₁)), rep(b))) = eval(App(App(t, rep(a₂)), rep(b)))`.
    3. By self-simulation:
       `atom(dot(a₁, b)) = atom(dot(a₂, b))`.
    4. By atom injectivity: `dot(a₁, b) = dot(a₂, b)`.
    5. Since this holds for all `b`, extensionality gives `a₁ = a₂`.

    This is the information-theoretic core of the self-simulation
    derivation: the self-simulator must maintain enough information in
    the partial application to reconstruct the full row. It cannot
    compress — each of the `n` elements must map to a distinct
    intermediate term. -/
theorem partial_app_injective (hss : SelfSimulates M) :
    ∃ t : Term n, ∀ a₁ a₂ : Fin n,
      M.eval (.app t (rep M.q M.top a₁)) =
      M.eval (.app t (rep M.q M.top a₂)) →
      a₁ = a₂ := by
  obtain ⟨t, ht⟩ := hss
  exact ⟨t, fun a₁ a₂ heq => M.extensional a₁ a₂ (fun x => by
    have h1 := ht a₁ x
    have h2 := ht a₂ x
    have h3 := M.eval_comp
      (.app t (rep M.q M.top a₁))
      (.app t (rep M.q M.top a₂))
      (rep M.q M.top x) heq
    have h4 : Term.atom (M.dot a₁ x) = Term.atom (M.dot a₂ x) := by
      calc Term.atom (M.dot a₁ x)
          = M.eval (.app (.app t (rep M.q M.top a₁)) (rep M.q M.top x)) := h1.symm
        _ = M.eval (.app (.app t (rep M.q M.top a₂)) (rep M.q M.top x)) := h3
        _ = Term.atom (M.dot a₂ x) := h2
    exact Term.atom_injective h4)⟩

/-- **Partial application distinctness**: distinct elements produce
    distinct intermediate terms under the self-simulator.

    Contrapositive of `partial_app_injective`. -/
theorem partial_app_distinct (hss : SelfSimulates M) :
    ∃ t : Term n, ∀ a₁ a₂ : Fin n, a₁ ≠ a₂ →
      M.eval (.app t (rep M.q M.top a₁)) ≠
      M.eval (.app t (rep M.q M.top a₂)) := by
  obtain ⟨t, ht⟩ := partial_app_injective M hss
  exact ⟨t, fun a₁ a₂ hne heq => hne (ht a₁ a₂ heq)⟩

/-- **Encoding injectivity**: self-simulation forces the Q-depth
    encoding to be injective.

    If `rep(a₁) = rep(a₂)`, then trivially `eval(App(t, rep(a₁)))` =
    `eval(App(t, rep(a₂)))`, so by partial application injectivity,
    `a₁ = a₂`.

    This means the Q-depth encoding must assign distinct representations
    to distinct elements — a basic feasibility requirement for
    self-simulation. -/
theorem rep_injective_of_self_sim (hss : SelfSimulates M) :
    ∀ a₁ a₂ : Fin n,
      rep M.q M.top a₁ = rep M.q M.top a₂ → a₁ = a₂ := by
  obtain ⟨t, ht⟩ := partial_app_injective M hss
  intro a₁ a₂ hrep
  exact ht a₁ a₂ (by rw [hrep])

/-- **Row determination**: self-simulation means each element's row
    is fully determined by its partial application. If two elements
    produce the same partial application, they must have identical rows. -/
theorem row_eq_of_partial_eq
    (t : Term n)
    (ht : ∀ a b : Fin n,
      M.eval (.app (.app t (rep M.q M.top a)) (rep M.q M.top b)) =
      .atom (M.dot a b))
    (a₁ a₂ : Fin n)
    (heq : M.eval (.app t (rep M.q M.top a₁)) =
           M.eval (.app t (rep M.q M.top a₂))) :
    ∀ x : Fin n, M.dot a₁ x = M.dot a₂ x := by
  intro x
  have h1 := ht a₁ x
  have h2 := ht a₂ x
  have h3 := M.eval_comp
    (.app t (rep M.q M.top a₁))
    (.app t (rep M.q M.top a₂))
    (rep M.q M.top x) heq
  have h4 : Term.atom (M.dot a₁ x) = Term.atom (M.dot a₂ x) := by
    calc Term.atom (M.dot a₁ x)
        = M.eval (.app (.app t (rep M.q M.top a₁)) (rep M.q M.top x)) := h1.symm
      _ = M.eval (.app (.app t (rep M.q M.top a₂)) (rep M.q M.top x)) := h3
      _ = Term.atom (M.dot a₂ x) := h2
  exact Term.atom_injective h4

end Theorems

end SelfSimulation
