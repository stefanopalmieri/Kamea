# The Defunctionalized CPS Continuation Protocol

This document specifies the continuation protocol used by the Ψ-Lisp meta-circular evaluator (`examples/psi_metacircular.lisp`). Every continuation is a tagged cons-list — never a closure. This makes the entire pending computation inspectable, serializable, and modifiable at runtime.

The protocol follows Reynolds (1972), Danvy & Nielsen (2001), and Smith (1984): a CPS meta-circular evaluator where every continuation has been defunctionalized into a tagged data structure, enabling the reflective tower operations (reify/reflect) that Smith's 3-Lisp introduced.

**Source**: all line references are to `examples/psi_metacircular.lisp`.

---

## 1. What Is a Continuation in This System

A continuation is a tagged cons-list of the form:

```
(tag value₁ value₂ ... next-k)
```

- **tag**: a symbol identifying the continuation type (e.g., `k-if`, `k-let-bind`).
- **values**: captured data — expressions yet to evaluate, environments, intermediate results.
- **next-k**: the enclosing continuation, always the last element. Following `next-k` pointers walks the chain back to `k-id`, which is the terminal frame.

The chain is a linked list of pending computation frames. At any moment during evaluation, the current continuation `k` describes everything the evaluator will do after the current sub-expression returns. The chain grows as evaluation descends into sub-expressions and shrinks as results propagate outward.

Because continuations are cons-lists, they support the full Lisp data API: `car` reads the tag, `cdr` reads the values, `nth` accesses any field, `cons`/`list` rebuilds frames. No special reflection API is needed — standard list operations are the reflection API.

### The two dispatch functions

The evaluator uses two dispatch functions:

- **`apply-k`** (line 138): dispatches on 12 standard continuation tags. Takes `(k, val)` — a continuation and the value being delivered to it.
- **`apply-k-top`** (line 268): dispatches on 2 toplevel continuation tags. Takes `(k, val, env)` — a continuation, a value, and an environment. The extra `env` argument threads `defun` bindings through toplevel evaluation.

The bridge between them is `k-top-wrap`: when `apply-k` encounters this tag, it calls `apply-k-top` with the enclosed toplevel continuation.

---

## 2. All 14 Continuation Types

### Standard continuations (dispatched by `apply-k`)

**k-id** — Identity / terminal

```
Shape:   (k-id)
Fields:  none
Created: by the caller as the outermost continuation
Dispatch: returns val unchanged (line 145)
```

The base case. Every continuation chain ends here. `apply-k(k-id, val)` = `val`.

---

**k-if** — If-test evaluated, choose branch

```
Shape:   (k-if then-expr else-expr env next-k)
Fields:  then-expr, else-expr, env, next-k
Created: meval on (if test then else), line 316
Dispatch: if val is non-NIL, meval then-expr; else meval else-expr (lines 150-158)
```

Created when `meval` encounters an `if` expression. The test sub-expression is evaluated with this continuation as `k`. When the test value arrives, `apply-k` branches: non-NIL takes `then-expr`, NIL takes `else-expr`, both evaluated in `env` with `next-k`.

---

**k-cond** — Cond clause test evaluated

```
Shape:   (k-cond rest-clauses consequent env next-k)
Fields:  rest-clauses, consequent, env, next-k
Created: eval-cond, line 388
Dispatch: if val is non-NIL, meval consequent; else try rest-clauses (lines 162-169)
```

Created when `eval-cond` evaluates the test of a `cond` clause. If the test passes, the consequent is evaluated. Otherwise, evaluation continues with the remaining clauses.

---

**k-let-body** — All let-bindings done, evaluate body

```
Shape:   (k-let-body body-expr next-k)
Fields:  body-expr, next-k
Created: meval on (let bindings body), line 329
Dispatch: meval body-expr with val as the environment (lines 174-177)
```

Created when `meval` encounters a `let` expression. The `eval-let-bindings` helper processes bindings one at a time (see `k-let-bind`), and when all bindings are done, delivers the extended environment as `val` to this continuation. `apply-k` then evaluates the body in that environment.

---

**k-let-bind** — One let-binding evaluated, continue binding

```
Shape:   (k-let-bind var-name rest-bindings env next-k)
Fields:  var-name, rest-bindings, env, next-k
Created: eval-let-bindings, line 394
Dispatch: extend env with (var-name . val), continue with rest-bindings (lines 182-189)
```

Created for each binding in a `let`. When the binding's value expression returns as `val`, `apply-k` conses `(var-name . val)` onto the environment and calls `eval-let-bindings` with the remaining bindings. This threads through the chain until no bindings remain, at which point the accumulated environment is delivered to `k-let-body`.

---

**k-seq** — Sequence element done, evaluate next

```
Shape:   (k-seq rest-exprs env next-k)
Fields:  rest-exprs, env, next-k
Created: eval-sequence, line 401
Dispatch: discard val, continue evaluating rest-exprs (lines 194-198)
```

Created for each non-final expression in a `progn`. The value of the current expression is discarded, and evaluation continues with the remaining expressions. The final expression in the sequence is evaluated directly with `next-k`, not through `k-seq`.

---

**k-apply-fn** — Function position evaluated, evaluate arguments

```
Shape:   (k-apply-fn arg-exprs env next-k)
Fields:  arg-exprs, env, next-k
Created: meval on function application (fn arg1 arg2 ...), line 357
Dispatch: val is the function; start evaluating args with k-do-apply (lines 203-208)
```

Created when `meval` encounters a function application. The function expression is evaluated first with this continuation. When the function value arrives as `val`, `apply-k` calls `eval-args` to evaluate the argument expressions, packaging `val` (the function) into a `k-do-apply` frame for use after all arguments are ready.

---

**k-do-apply** — All arguments evaluated, apply function

```
Shape:   (k-do-apply fn next-k)
Fields:  fn, next-k
Created: apply-k on k-apply-fn, line 208
Dispatch: call mapply(fn, val, next-k) where val is the argument list (lines 213-216)
```

Created by the `k-apply-fn` dispatch. When all arguments have been evaluated (delivered as a list in `val`), `apply-k` calls `mapply` to apply the function. For closures, `mapply` extends the closure's environment with parameter bindings and evaluates the body. For builtins, `mapply` calls `apply-builtin` directly.

---

**k-args-head** — First argument evaluated, evaluate rest

```
Shape:   (k-args-head rest-exprs env next-k)
Fields:  rest-exprs, env, next-k
Created: eval-args, line 382
Dispatch: val is the first arg; evaluate rest with k-args-tail (lines 221-226)
```

Created by `eval-args` when there is at least one argument expression. The first argument is evaluated with this continuation. When its value arrives, `apply-k` calls `eval-args` on the remaining expressions, packaging the first value into a `k-args-tail` frame.

---

**k-args-tail** — Remaining arguments evaluated, cons onto list

```
Shape:   (k-args-tail head-val next-k)
Fields:  head-val, next-k
Created: apply-k on k-args-head, line 226
Dispatch: cons head-val onto val (the rest), deliver to next-k (lines 231-234)
```

Created by the `k-args-head` dispatch. When the remaining arguments have been evaluated (delivered as a list in `val`), `apply-k` conses the saved first value onto the front, producing the complete argument list, and delivers it to `next-k` (typically `k-do-apply`).

---

**k-reflect-state** — Reflect: state evaluated, evaluate value

```
Shape:   (k-reflect-state value-expr env)
Fields:  value-expr, env
Created: meval on (reflect state value), line 352
Dispatch: val is the state; evaluate value-expr with k-reflect-jump (lines 239-243)
```

Created when `meval` encounters a `reflect` expression. The state expression is evaluated first. When the state arrives as `val`, `apply-k` evaluates the value expression with a `k-reflect-jump` continuation that captures the state. **Note**: this frame has no `next-k` — reflect abandons the current continuation chain.

---

**k-reflect-jump** — Reflect: value evaluated, jump to saved continuation

```
Shape:   (k-reflect-jump state)
Fields:  state
Created: apply-k on k-reflect-state, line 243
Dispatch: extract saved-k from state, call apply-k(saved-k, val) (lines 248-251)
```

Created by the `k-reflect-state` dispatch. When the value arrives, `apply-k` extracts the continuation from the saved state (`(car (cdr state))`) and jumps to it, delivering `val`. This is the mechanism by which `reflect` abandons the current future and resumes a previously-reified one — possibly modified.

---

### Toplevel continuations (dispatched by `apply-k-top`)

**k-top-wrap** — Bridge from standard to toplevel protocol

```
Shape:   (k-top-wrap menv top-k)
Fields:  menv, top-k
Created: meval-toplevel for non-defun forms, line 422
Dispatch: call apply-k-top(top-k, val, menv) (lines 257-260)
```

Created when `meval-toplevel` evaluates a non-`defun` form. It wraps a toplevel continuation `top-k` (which expects `(val, env)`) inside a standard continuation (which delivers only `val`). When `apply-k` encounters this tag, it calls `apply-k-top` with the saved environment, bridging the two protocols.

---

**k-program-step** — Continue with remaining toplevel forms

```
Shape:   (k-program-step rest-exprs final-k)
Fields:  rest-exprs, final-k
Created: meval-program, line 428
Dispatch: if rest is empty, deliver val to final-k; else evaluate next form (lines 278-283)
```

Created by `meval-program` to thread through a sequence of toplevel forms. After each form is evaluated (with its environment update for `defun`s), `apply-k-top` either continues with the remaining forms or delivers the final value.

---

## 3. Worked Example: `(if (null NIL) 42 99)`

We trace `meval('(if (null NIL) 42 99), base-env, (k-id))` step by step.

Note: `zerop` is not in the meta-evaluator's base environment. We use `(null NIL)` instead — `null` tests for the empty/false value, and `NIL` is that value, so `(null NIL)` returns `T`. The structure is identical to `(if (zerop 0) 42 99)`.

Notation: `env` abbreviates `base-env` throughout. Symbol IDs (the integers ≥ 100 that represent quoted symbols) are written as their names for readability.

### Step 1 — meval receives the if-expression

```
meval( (if (null NIL) 42 99), env, (k-id) )
```

The expression is compound with head `if`. Extract branches:
- test = `(null NIL)`
- then-branch = `42`
- else-branch = `99`

Create a `k-if` frame and evaluate the test:

```
→ meval( (null NIL), env, (k-if 42 99 env (k-id)) )
```

**Chain**: `k-if → k-id`

### Step 2 — meval receives the function application `(null NIL)`

```
meval( (null NIL), env, (k-if 42 99 env (k-id)) )
```

Compound expression with head `null`. Not a special form — fall through to function application. Evaluate the function position:

```
→ meval( null, env, (k-apply-fn (NIL) env (k-if 42 99 env (k-id))) )
```

**Chain**: `k-apply-fn → k-if → k-id`

### Step 3 — meval looks up `null`

```
meval( null, env, (k-apply-fn (NIL) env (k-if 42 99 env (k-id))) )
```

`null` is a symbol (integer ≥ 100). Look up in `env` → the builtin `(91 null)`. Deliver to continuation:

```
→ apply-k( (k-apply-fn (NIL) env (k-if 42 99 env (k-id))), ⟨builtin:null⟩ )
```

### Step 4 — apply-k dispatches k-apply-fn

```
apply-k( (k-apply-fn (NIL) env (k-if 42 99 env (k-id))), ⟨builtin:null⟩ )
```

Tag is `k-apply-fn`. The function value `⟨builtin:null⟩` has arrived. Now evaluate the argument expressions `(NIL)`, packaging the function into a `k-do-apply` frame:

```
→ eval-args( (NIL), env, (k-do-apply ⟨builtin:null⟩ (k-if 42 99 env (k-id))) )
```

**Chain**: `k-do-apply → k-if → k-id`

### Step 5 — eval-args processes the single argument `NIL`

```
eval-args( (NIL), env, (k-do-apply ⟨builtin:null⟩ (k-if 42 99 env (k-id))) )
```

One argument expression: `NIL`. Remaining: none. Evaluate the first argument:

```
→ meval( NIL, env, (k-args-head () env (k-do-apply ⟨builtin:null⟩ (k-if 42 99 env (k-id)))) )
```

**Chain**: `k-args-head → k-do-apply → k-if → k-id`

### Step 6 — meval evaluates NIL

```
meval( NIL, env, (k-args-head () env (k-do-apply ...)) )
```

`NIL` is null. Deliver immediately:

```
→ apply-k( (k-args-head () env (k-do-apply ...)), NIL )
```

### Step 7 — apply-k dispatches k-args-head

```
apply-k( (k-args-head () env (k-do-apply ...)), NIL )
```

Tag is `k-args-head`. The first argument evaluated to `NIL`. Remaining expressions: `()` (empty). Evaluate the rest, packaging the first value into `k-args-tail`:

```
→ eval-args( (), env, (k-args-tail NIL (k-do-apply ...)) )
```

**Chain**: `k-args-tail → k-do-apply → k-if → k-id`

### Step 8 — eval-args on empty list

```
eval-args( (), env, (k-args-tail NIL (k-do-apply ...)) )
```

No more arguments. Deliver the empty list:

```
→ apply-k( (k-args-tail NIL (k-do-apply ...)), () )
```

### Step 9 — apply-k dispatches k-args-tail

```
apply-k( (k-args-tail NIL (k-do-apply ...)), () )
```

Tag is `k-args-tail`. Cons the saved head value onto the rest:

```
(cons NIL ()) = (NIL)
→ apply-k( (k-do-apply ⟨builtin:null⟩ (k-if 42 99 env (k-id))), (NIL) )
```

**Chain**: `k-do-apply → k-if → k-id`

### Step 10 — apply-k dispatches k-do-apply

```
apply-k( (k-do-apply ⟨builtin:null⟩ (k-if 42 99 env (k-id))), (NIL) )
```

Tag is `k-do-apply`. Function is `⟨builtin:null⟩`, argument list is `(NIL)`. Call `mapply`:

```
→ mapply( ⟨builtin:null⟩, (NIL), (k-if 42 99 env (k-id)) )
```

### Step 11 — mapply applies the builtin

```
mapply( ⟨builtin:null⟩, (NIL), (k-if 42 99 env (k-id)) )
```

`⟨builtin:null⟩` is a builtin. Dispatch:

```
apply-builtin(null, (NIL)) → (null NIL) → T
→ apply-k( (k-if 42 99 env (k-id)), T )
```

**Chain**: `k-if → k-id`

### Step 12 — apply-k dispatches k-if (the critical moment)

```
apply-k( (k-if 42 99 env (k-id)), T )
```

Tag is `k-if`. The test value is `T` (non-NIL). **Take the then-branch**:

```
→ meval( 42, env, (k-id) )
```

**Chain**: `k-id`

### Step 13 — meval evaluates 42

```
meval( 42, env, (k-id) )
```

`42` is self-evaluating (< 100). Deliver:

```
→ apply-k( (k-id), 42 )
```

### Step 14 — apply-k dispatches k-id

```
apply-k( (k-id), 42 )
```

Tag is `k-id`. Return `42`.

**Result: 42**

### Chain evolution summary

```
Step  Chain (outermost → innermost)
 1    k-id
 2    k-if → k-id
 3    k-apply-fn → k-if → k-id
 4    (dispatch k-apply-fn)
 5    k-args-head → k-do-apply → k-if → k-id
 6    (deliver NIL)
 7    (dispatch k-args-head)
 8    k-args-tail → k-do-apply → k-if → k-id
 9    (dispatch k-args-tail, cons)
10    (dispatch k-do-apply)
11    (mapply builtin, returns T)
12    (dispatch k-if, val=T, take then-branch)
13    k-id
14    (dispatch k-id, return 42)
```

The chain grows to depth 4 (step 5: args-head → do-apply → if → id), then contracts as intermediate results propagate, until only `k-id` remains. This is the CPS equivalent of the call stack growing and shrinking.

---

## 4. The Branch Swap

This section traces the reflective tower's branch swap (`examples/psi_reflective_tower.lisp`, lines 279-310). A program evaluates `(if TEST 42 99)` where the test sub-expression reifies, finds the `k-if` frame in the continuation chain, swaps the then/else branches, and reflects. The result is 99 instead of 42, even though the test value is truthy.

### The expression

```lisp
(if (let ((s (reify)))
      (if (numberp s)
        s                           ;; second pass: return test value
        ;; first pass: find and modify k-if, then reflect
        (let ((k    (car (cdr s))))           ;; k = current continuation
          (let ((kb  (nth 4 k)))              ;; kb = k-let-body (via k-let-bind)
            (let ((kif (nth 2 kb)))           ;; kif = the k-if frame
              ;; Swap then/else in kif:
              (let ((swapped-kif (list (nth 0 kif) (nth 2 kif) (nth 1 kif)
                                       (nth 3 kif) (nth 4 kif))))
                ;; Rebuild chain with swapped kif:
                (let ((new-kb (list (nth 0 kb) (nth 1 kb) swapped-kif)))
                  (let ((new-k (list (nth 0 k) (nth 1 k) (nth 2 k)
                                     (nth 3 k) new-kb)))
                    (let ((new-state (list (car s) new-k (nth 2 s) (nth 3 s))))
                      (reflect new-state 1))))))))))
    42    ;; ORIGINAL then-branch
    99)   ;; ORIGINAL else-branch
```

### The continuation chain at the moment of reify

When `meval` encounters `(reify)` inside the test position of the outer `if`, the continuation `k` encodes everything that will happen after the test returns. The chain at this moment is:

```
k-let-bind      →  k-let-body     →  k-if          →  ...  →  k-id
(bind s, rest,      (body of let,     (42, 99,
 env, next-k)        next-k)           env, next-k)
```

Concretely:

```
Frame 0: (k-let-bind  <sym:s>  ()  env  Frame1)
         The let is binding s. No remaining bindings. env is the current environment.

Frame 1: (k-let-body  <body-of-inner-if>  Frame2)
         Once s is bound, evaluate the body (the inner if).

Frame 2: (k-if  42  99  env  <next-k>)
         The OUTER if. then=42, else=99. This is the target.

Frame 3+: ... → k-id
         The remaining chain (toplevel bridge frames, ultimately k-id).
```

### What reify does

When `meval` encounters `(reify)` (line 343-344), it does:

```lisp
(apply-k k (list 'reified-state k menv expr))
```

It delivers a **reified state** to the current continuation `k`. The reified state is a 4-element list:

```
(reified-state  <continuation>  <environment>  <expression>)
```

- `<continuation>` is `k` itself — the tagged cons-list chain shown above.
- `<environment>` is `menv` — the meta-evaluator's current environment (an alist).
- `<expression>` is `expr` — the full `(reify)` expression.

This value flows through the continuation chain normally. `k` is `k-let-bind`, which binds `s` to the reified state. Then `k-let-body` evaluates the inner `if`.

### First pass: s is the reified state

The inner `if` tests `(numberp s)`. The reified state is a list, not a number, so `numberp` returns NIL. The else-branch executes: the program navigates the continuation chain.

### Navigating the chain

```lisp
(let ((k   (car (cdr s))))    ;; k = Frame 0 (k-let-bind)
  (let ((kb  (nth 4 k)))      ;; kb = Frame 1 (k-let-body), the next-k of k-let-bind
    (let ((kif (nth 2 kb)))   ;; kif = Frame 2 (k-if), the next-k of k-let-body
```

The code extracts:
- `k` = the continuation from the reified state = `(k-let-bind <sym:s> () env Frame1)`
- `kb` = `(nth 4 k)` = Frame 1 = `(k-let-body <body> Frame2)` — the 5th element (0-indexed: position 4) of the k-let-bind frame, which is its `next-k`
- `kif` = `(nth 2 kb)` = Frame 2 = `(k-if 42 99 env <next>)` — the 3rd element (position 2) of the k-let-body frame, which is its `next-k`

### The swap

The original k-if frame:

```
(k-if  42  99  env  <next-k>)
 tag   ↑   ↑   ↑    ↑
       │   │   │    └── enclosing continuation
       │   │   └── environment for evaluating branches
       │   └── else-branch (expression)
       └── then-branch (expression)
```

The swap creates a new k-if with then and else exchanged:

```lisp
(list (nth 0 kif)    ;; tag:  k-if         (unchanged)
      (nth 2 kif)    ;; then: 99           (was else)
      (nth 1 kif)    ;; else: 42           (was then)
      (nth 3 kif)    ;; env:  env          (unchanged)
      (nth 4 kif))   ;; next: <next-k>     (unchanged)
```

Result: `(k-if 99 42 env <next-k>)` — branches swapped.

### Rebuilding the chain

The swapped k-if must be stitched back into the chain. Each frame is rebuilt bottom-up:

```lisp
;; New k-let-body pointing to swapped k-if:
(list (nth 0 kb) (nth 1 kb) swapped-kif)
= (k-let-body <body> (k-if 99 42 env <next-k>))

;; New k-let-bind pointing to new k-let-body:
(list (nth 0 k) (nth 1 k) (nth 2 k) (nth 3 k) new-kb)
= (k-let-bind <sym:s> () env (k-let-body <body> (k-if 99 42 env <next-k>)))

;; New reified state with modified continuation:
(list (car s) new-k (nth 2 s) (nth 3 s))
= (reified-state <new-chain> <env> <expr>)
```

### Reflect with the modified chain

```lisp
(reflect new-state 1)
```

When `meval` encounters `reflect` (lines 350-352), it:

1. Evaluates the state expression → `new-state` (the modified reified state)
2. Creates `(k-reflect-state <value-expr> env)` to evaluate the value expression
3. Evaluates the value expression `1` → delivers `1` to `k-reflect-jump`

`apply-k` on `k-reflect-jump` (lines 248-251):

```lisp
(let ((saved-k (car (cdr state))))   ;; extract continuation from state
  (apply-k saved-k val))             ;; jump to it with val=1
```

`saved-k` is the **modified** continuation chain: `k-let-bind → k-let-body → k-if(99, 42, ...) → ...`

The value `1` is delivered to `k-let-bind`, which binds `s` to `1`.

### Second pass: s is the number 1

Now `s = 1`. The inner `if` tests `(numberp s)` → `T`. The then-branch returns `s` = `1`.

This value `1` flows to `k-let-body`, which evaluates the body. The body returns `1`, which is then delivered to the **swapped** `k-if`:

```
apply-k( (k-if 99 42 env <next-k>), 1 )
```

### apply-k dispatches the swapped k-if

Tag is `k-if`. The test value is `1` (non-NIL, i.e., truthy). `apply-k` takes the **then-branch**:

```lisp
(meval then-b env next-k)
```

But `then-b` is now `99` (it was swapped from the else position). So:

```
→ meval(99, env, <next-k>)
→ apply-k(<next-k>, 99)
→ ... → 99
```

**Result: 99**

The program wrote `(if TEST 42 99)`. The test value was `1` (truthy). The result was `99` (the original else-branch). The program rewrote its own control flow by modifying a data structure.

---

## 5. Reify and Reflect

### Reify

When `meval` encounters `(reify)` (line 343):

```lisp
((= head 'reify)
  (apply-k k (list 'reified-state k menv expr)))
```

It does **not** suspend evaluation. It delivers a value to the current continuation — that value happens to be a snapshot of the evaluator's state. The reified state is:

```
(reified-state  k  menv  expr)
      │         │   │     │
      │         │   │     └── the (reify) expression itself
      │         │   └── the meta-environment: an alist of (symbol . value) pairs
      │         └── the current continuation: a tagged cons-list chain
      └── tag identifying this as a reified state
```

The continuation `k` is the key component. It is the chain of pending computation frames, each a tagged cons-list, linked through `next-k` pointers. It encodes everything the evaluator will do after this point.

The environment `menv` is an association list: `((sym₁ . val₁) (sym₂ . val₂) ...)`. Each value is either a number, NIL, T, a closure `(90 name params body env)`, or a builtin `(91 name)`.

### Reflect

When `meval` encounters `(reflect state-expr value-expr)` (lines 350-352):

```lisp
((= head 'reflect)
  (meval (car (cdr expr)) menv
    (list 'k-reflect-state (car (cdr (cdr expr))) menv)))
```

Two-phase evaluation:

**Phase 1**: Evaluate `state-expr` with continuation `(k-reflect-state value-expr env)`. The current continuation `k` is **discarded** — it does not appear in the `k-reflect-state` frame. This is the point of no return: the current future is abandoned.

**Phase 2**: When the state arrives, `apply-k` on `k-reflect-state` evaluates `value-expr` with continuation `(k-reflect-jump state)`.

**Phase 3**: When the value arrives, `apply-k` on `k-reflect-jump` extracts the saved continuation from the state and jumps to it:

```lisp
(let ((saved-k (car (cdr state))))
  (apply-k saved-k val))
```

The saved continuation may be the original one from `reify`, or a modified copy. The evaluator doesn't know or care — it simply dispatches on the tags it finds. If the tags are valid continuation types, `apply-k` processes them. The modification is invisible to the dispatch mechanism.

### The reify/reflect cycle

A typical pattern:

```lisp
(let ((s (reify)))
  (if (numberp s)
    (+ s 50)           ;; second pass: s is the reflected value
    (reflect s 7)))    ;; first pass: s is the reified state, reflect with 7
```

**First pass**: `(reify)` delivers the reified state to `k-let-bind`. `s` is bound to the state. `(numberp s)` is NIL (a list is not a number). The else-branch executes `(reflect s 7)`.

`reflect` evaluates `s` (the state, containing the continuation chain that leads through `k-let-bind → k-let-body → k-id`). Then evaluates `7`. Then jumps to the saved continuation with value `7`.

**Second pass**: The saved continuation is `k-let-bind`. It binds `s` to `7`. Then `k-let-body` evaluates the body. `(numberp s)` is T (7 is a number). The then-branch returns `(+ 7 50)` = `57`.

**Result: 57**

---

## 6. Serialization Properties

Every continuation in this system is a tagged cons-list built from:
- Integers (tag symbol IDs, literal values)
- NIL
- Cons cells

There are no closures, no function pointers, no opaque runtime objects in the continuation chain. This is a direct consequence of defunctionalization: every lambda that would have appeared in a standard CPS evaluator has been replaced by a data constructor (the tag) and a case in the dispatch function (`apply-k`).

This yields three properties that closure-based continuations lack:

**Serializable.** The entire pending computation can be written to a byte stream and reconstructed. Since continuations are cons-lists and cons-lists are built from Ψ∗ terms (pairs of Q-chain integers and g-constructor pairs), the continuation is already in the algebra's native representation. Writing a continuation to disk is the same operation as writing any other Ψ∗ value.

**Diffable.** Two continuations can be structurally compared. Given two reified states from different points in a computation, standard list comparison identifies exactly which frames differ and how. The branch swap produces a diff of exactly one frame (the k-if) with exactly two fields exchanged.

**Transmittable.** A continuation can be sent to another machine and resumed there, provided the receiver has the same `apply-k` dispatch function. The continuation carries no pointers into the sender's address space — it is pure data. This is the mechanism by which checkpoint/restart could work: reify the state, serialize the continuation and environment, transmit, deserialize, reflect.

Note that the **environment** is also an association list (pure data), and **closures** are 5-element lists `(90 name params body env)` where `body` is an S-expression and `env` is an alist. The entire evaluator state — continuation, environment, closures, pending expressions — is serializable. There is nothing opaque anywhere in the system.

This is not an incidental property. It is the architectural consequence of three design choices: (1) defunctionalized continuations (Reynolds → Danvy & Nielsen), (2) first-class environments as alists (not hash tables or stack frames), and (3) closures as tagged data (not runtime function objects). Smith's 3-Lisp required inspectable state but achieved it through an infinite tower of interpreters. Defunctionalization achieves it through finite data structures — the tower is in the tags, not in the interpreters.
