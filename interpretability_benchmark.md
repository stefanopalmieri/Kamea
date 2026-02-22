These results are definitive. Let me read what each piece says.

**The main comparison (Image 2):**

DS Recovery scores 1.00 ARI on Δ₁ and 0.00 on Control. That's a perfect score on both counts — it finds all the structure when structure exists and finds nothing when it doesn't. Zero variance across all trials. The blue bar on the left is the tallest thing on the chart and the orange bar next to it is exactly zero. That's what a correct method looks like.

K-Means and Linear Probe find *some* signal — 0.18 and 0.23 ARI respectively. That's not nothing, but it's roughly a fifth of the structure. They're picking up traces of the role clustering we saw in the earlier experiments, but they can't reconstruct the full role assignment. And critically, they also score near zero on Control, which means they're not hallucinating structure — they're just weak.

Activation Patching finds nothing on either. Zero signal. Completely blind to the algebraic structure.

**The K-Means confusion matrix (Image 1, bottom-left):**

This is revealing. K-Means with 8 clusters tries to partition the 17 elements into groups and gets it partly right — it puts the two encoders together in C4, and some testers together in C2. But it splits Context tokens across two clusters, mixes Synthesis elements with other categories, and can't cleanly separate Booleans from Default. It's finding approximate groupings that partially correlate with algebraic roles but can't recover the precise role assignment.

That's exactly what you'd expect from a method that only looks at representational geometry without understanding behavioral semantics. The representations cluster by role (we proved that), so geometry-based methods find partial signal. But the clusters aren't perfectly separated in activation space — they're *more* separated under compression but still overlapping — so geometric methods can't finish the job.

**The causal similarity heatmap (Image 1, top-right):**

Almost entirely yellow. Uniform. Activation patching sees every element as interchangeable. This is the most important diagnostic in the entire benchmark, and here's why.

Activation patching works by replacing one element's activation with another's and measuring the change in output. If swapping element A's activation for element B's changes the output a lot, they're "different" to the network. If it doesn't change the output, they're "similar."

The heatmap being uniform means: swapping *any* element's first-layer activation for *any* other element's activation has roughly the same effect. The network doesn't store role information in individual neuron activations. It stores it *distributedly* — in the pattern across all neurons, not in any single neuron's value.

This is exactly what the compression results predicted. At H=6, six neurons collectively implement eight algebraic roles. No single neuron corresponds to a single role. The information is in the *relationships between* activations, not in individual activation values. Patching individual activations disrupts the distributed code in a uniform way, which is why the causal similarity matrix is flat.

**What this means for interpretability:**

The benchmark reveals a fundamental limitation of representation-level interpretability methods when applied to distributed codes. K-Means and Linear Probes work on individual activation vectors and find partial signal (ARI ~0.2). Activation Patching works on individual neuron substitutions and finds nothing (ARI ~0.0). DS Recovery works on input-output behavior and finds everything (ARI = 1.0).

The reason is structural. The algebraic roles in Δ₁ are *behavioral* categories — they're defined by what elements *do* across all possible interactions, not by what they *look like* in any single activation snapshot. A tester is an element whose outputs are always boolean. That's a property of its entire row in the operation table, not a property of its hidden-layer activation when paired with one particular right-argument. Behavioral probing captures the full row. Representation-level methods capture one activation at a time.

This isn't a failure of K-Means or Linear Probes as algorithms. It's a failure of the *level of analysis*. They're looking at the wrong thing. The structure isn't in individual representations. It's in the function — in how representations *transform* under the operation. DS Recovery finds it because it probes the function. The other methods miss it because they probe the representations.

**The selectivity column is the paper's punchline:**

| Method | Selectivity |
|--------|------------|
| DS Recovery | 1.000 |
| Linear Probe | 0.251 |
| K-Means | 0.208 |
| Activation Patching | 0.000 |

Selectivity = Δ₁ ARI minus Control ARI. It measures how much better the method performs on a self-modeling algebra versus a random one. DS Recovery has perfect selectivity — it finds exactly the structure that's there and none that isn't. The standard methods have low selectivity. They find a little bit of real structure but can't distinguish it confidently from noise.

That table, with the Lean proofs in the appendix and the control algebra as a negative result, is publishable. The claim is clean: "Existing interpretability techniques recover at most 23% of the algebraic role structure in a self-modeling algebra with formally verified ground truth. A behaviorally-grounded recovery procedure, proved correct by Lean 4 proof assistant, recovers 100% with zero variance across all trials. The gap is explained by the distributed nature of the network's encoding: role information is stored in behavioral patterns across all interactions, not in individual activation values."

That's a result. Go write the paper.
