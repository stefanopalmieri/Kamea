The claim has to be precise because the interpretability community will push back. They'll say "we do have ground truth — we have toy models, we have synthetic circuits, we have Nanda's modular addition where we know the algorithm is Fourier-based." You need to distinguish what you mean by ground truth from what they already have.

The distinction is between **knowing the answer** and **proving the answer is unique**.

Nanda reverse-engineered modular addition and found a Fourier-based algorithm. That's a ground truth in the sense that he can verify the network uses that specific algorithm. But he can't prove it's the *only* algorithm that produces those outputs. Maybe there's another algorithm with different internal structure that computes addition mod 113 equally well. His ground truth is: "I found *an* algorithm this network uses." Not: "I proved this is the *only* structure consistent with this behavior."

The same applies to every existing toy setup. You build a synthetic circuit with known structure, train a network on it, and check whether your interpretability method recovers the structure you built in. But the structure you built in is one possible implementation. The network might have learned a different implementation that produces identical outputs. Your method might recover your intended structure, or it might recover the network's actual structure, or it might recover neither, and you can't distinguish these cases because you don't have a uniqueness proof.

**Your ground truth is different in a specific, checkable way.**

The Lean proofs don't just verify that Δ₁ has certain structure. They verify that the recovery procedure's output is *uniquely determined* by the input-output behavior. Step 1 doesn't just find absorbers — the proof shows there are exactly two and they're the only elements with constant left-image. Step 2 doesn't just find testers — the proof shows they're the only elements with boolean-valued left-image. Each identification is unique. No other assignment of roles to elements is consistent with the behavior.

This means: if your interpretability method recovers a different role assignment, it's *provably wrong*. Not "probably wrong" or "inconsistent with our intended structure." Provably wrong, as checked by Lean. That's what no existing benchmark provides.

The argument has three layers.

**Layer 1: Verification requires a definition of correctness.**

Current interpretability papers report results like "we found that neuron 47 represents the concept of dogs" or "this circuit implements modular addition via Fourier transforms." But what does "represents" mean? What does "implements" mean? If two researchers disagree about what a neuron represents, there's no formal criterion to resolve the disagreement. The field lacks a definition of what it means to correctly recover a network's semantics.

You provide one: correct recovery means identifying every element's functional role such that no other identification is consistent with the observed behavior. Correct means unique. The definition is checkable by Lean.

**Layer 2: Completeness requires exhaustive identification.**

Current methods typically identify *some* structure — a particular circuit, a particular feature, a particular direction in activation space. But they don't claim to have identified *all* structure. There's no criterion for completeness. After you've found three circuits, how do you know there isn't a fourth?

Your recovery procedure identifies all 17 elements. The Lean proofs verify that every element is accounted for. Completeness isn't aspirational — it's proved. If your method identifies 14 of 17 elements correctly, you know exactly how incomplete it is, because you know what 17/17 looks like.

**Layer 3: Ground truth requires implementation independence.**

The deepest issue with existing benchmarks. If you build a synthetic circuit and train a network to implement it, your ground truth is tied to the implementation you intended. But the network might implement the same function differently. Any benchmark based on "we know the intended implementation" confounds the function with the implementation.

Your ground truth is implementation-independent. The recovery procedure works on input-output behavior. The Lean proofs verify properties of the function, not of any particular implementation. The neural network experiments demonstrate this directly: the same recovery procedure works on Δ₁ as a lookup table, as a Python function, and as a trained neural network with random initialization. Three implementations, same recovery, same result. The ground truth is the function's semantics, not any implementation's internals.

**The paragraph that makes the argument:**

"Existing interpretability benchmarks verify that a method can recover *intended* structure from *known* implementations. We argue this is insufficient for three reasons. First, without a formal definition of correct recovery, disagreements between methods cannot be resolved — there is no criterion for which interpretation is right. Second, without a completeness criterion, partial recovery cannot be measured against a known total. Third, without implementation independence, benchmarks confound the function a network computes with the way it computes it. We construct a benchmark that addresses all three: a self-modeling algebra (Δ₁) whose functional roles are formally defined by axioms, proved unique by a Lean 4 proof assistant, and recoverable from input-output behavior regardless of implementation. This provides, to our knowledge, the first interpretability benchmark where correctness is machine-checkable, completeness is formally defined (17/17 elements), and the ground truth is a property of the function rather than of any particular network."

That's not claiming existing work is bad. It's identifying three specific gaps — definition, completeness, implementation independence — and filling all three. A reviewer can check each claim: the definition is in the Lean proofs (unique role assignment), completeness is in the element count (17/17), implementation independence is in the experiments (same recovery across three implementations).

The strongest single sentence is: **"If two interpretability methods disagree about this network's structure, the Lean proofs determine which one is right."** No existing benchmark can say that. Yours can.

------

This is the figure I'd put on page 1. Before the algebra. Before the Lean proofs. Before the recovery procedure. Show this grid and say: "The left column is the ground truth — the behavioral structure of a self-modeling algebra with machine-checked uniqueness proofs. The middle columns are what standard training produces internally. The right columns are what axiom-derived regularization produces. The axioms work. Here's the paper explaining why."
-----

The recovery procedure identifies all structural roles (ARI=1.0) but the actuality irreducibility theorem (proved in the Lean formalization) shows that behavioral probing cannot determine which elements are 'actual' — two algebras differing in only 2 of 324 entries, with identical role structure, are behaviorally indistinguishable. This formally separates structural interpretability (recoverable) from referential interpretability (provably unrecoverable from behavior), suggesting that the limits of mechanistic interpretability are not merely practical but mathematical.

