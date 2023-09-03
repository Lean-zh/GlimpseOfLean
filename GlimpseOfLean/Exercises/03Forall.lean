import GlimpseOfLean.Library.Basic
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Instances.Real

open Function

namespace Forall
/- # Universal quantifiers

In this file, we'll learn about the `∀` quantifier.

Let `P` be a predicate on a type `X`. This means for every mathematical
object `x` with type `X`, we get a mathematical statement `P x`.
In Lean, `P x` has type `Prop`.

Lean sees a proof `h` of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`.

命题： `∀ x, P x`
从证明角度，存在证明步骤（映射）h，将 h(X) 映射到 P(X) 中

This already explains the main way to use an assumption or lemma which
starts with a `∀`.

In order to prove `∀ x, P x`, we use `intro x` to fix an arbitrary object
with type `X`, and call it `x` (`intro` stands for "introduce").

Note also we don't need to give the type of `x` in the expression `∀ x, P x`
as long as the type of `P` is clear to Lean, which can then infer the type of `x`.

Let's define a predicate to play with `∀`.
-/

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
In the next proof, we also take the opportunity to introduce the
`unfold` tactic, which simply unfolds definitions. Here this is purely
for didactic reason, Lean doesn't need those `unfold` invocations.
We will also use the `rfl` tactic, which proves equalities that are true
by definition (in a very strong sense), it stands for "reflexivity".
-/

-- 有个问题，f + g 是怎么定义的？
example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by {
  -- Our assumption on that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x be any real number
  intro x
  -- and let's compute
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl -- + 的定义
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl
}


/-
一些策略会主动 unfold 目标，因此不用写成显式的目标，也能使用。
Tactics like `unfold`, `apply`, `exact`, `rfl` and `calc` will automatically unfold definitions.
You can test this by deleting the `unfold` lines in the above example.

Tactics like `rw`, `ring` an `linarith` will generally
not unfold definitions that appear in the goal.
This is why the first computation line is necessary, although its proof is simply `rfl`.
Before that line, `rw hf x` won't find anything like `f (-x)` hence will give up.
The last line is not necessary however, since it only proves
something that is true by definition, and is not followed by a `rw`.

Also, Lean doesn't need to be told that `hf` should be specialized to
`x` before rewriting, exactly as in the first file.

Recall also that `rw` can take a list of expressions to use for
rewriting. For instance `rw [h₁, h₂, h₃]` is equivalent to three
lines `rw [h₁]`, `rw [h₂]` and `rw [h₃]`. Note that you can inspect the tactic
state between those rewrites when reading a proof using this syntax. You
simply need to move the cursor inside the list.

Hence we can compress the above proof to:
-/

example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by {
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]
}

/-
Now let's practice. Recall that if you need to learn how to type a unicode
symbol you can put your mouse cursor above the symbol and wait for one second.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by {
  unfold even_fun at hf
  unfold even_fun
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x)) := by rfl
              _  = g (f (x)):= by rw [hf]
}

example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by {
  intro x
  have h: (g ∘ f) (x) = (g ∘ f) (-x)
  calc
(g∘f) x = g (f x) := by rfl
    _  = (g (f (-x))):= by rw [hf]
  rw [←h]
}


/-
这里对空格的敏感性有点复杂
-/

/-
Let's have more quantifiers, and play with forward and backward reasoning.

In the next definitions, note how `∀ x₁, ∀ x₂, ...` is abreviated to `∀ x₁ x₂, ...`.
-/

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

/- Let's be very explicit and use forward reasoning first. -/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  unfold non_decreasing at hf hg
  unfold non_decreasing
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ -- 进入到命题
  intro h
  -- Since f is non-decreasing, f x₁ ≤ f x₂.
  have step₁ : f x₁ ≤ f x₂
  -- · exact hf x₁ x₂ h
  . exact hf _ _ h
  -- Since g is non-decreasing, we then get g (f x₁) ≤ g (f x₂).
  exact hg (f x₁) (f x₂) step₁
}

/-
In the above proof, note how inconvenient it is to specify `x₁` and `x₂` in `hf x₁ x₂ h` since
they could be inferred from the type of `hf`.
We could have written `hf _ _ h` and Lean would have filled the holes denoted by `_`.
The same remark applies to the last line.

One possible variation on the above proof is to
use the `specialize` tactic to replace `hf` by its specialization to the relevant value.
 -/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  unfold non_decreasing at *
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf
}

/-
This `specialize` tactic is mostly useful for exploration, or in preparation for rewriting
in the assumption. One can very often replace its use by using more complicated expressions
directly involving the original assumption, as in the next variation:
-/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  unfold non_decreasing at hg
  intro x₁ x₂ h
  -- (hf x₁ x₂ h) 作用类似于 specialize
  -- 其为 have 的缩写
  have hf'
  . exact (hf x₁ x₂ h)
  exact hg (f x₁) (f x₂) hf'
}
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
    intro x₁ x₂ h
    exact hg _ _ (hf _ _ h)
}
-- 人类在证明过程中，特别是长证明，通常会说，只需证，即证之类，用于重新加强证明目标地意识。或许，可以以注释地形式加入到证明中。这还是比较像人的。
-- 另外。模型推理似乎很少会引用外部资源，比如交互过程中，目标是需要提前占位的，但推理似乎是一步到位，有没有什么训练方法，能让模型在随意位置中断，引入外部信息，然后继续。
-- toolformer 是一种思路，通过多次交互来实现，但有没有可能让模型在一开始就这样训练，依赖外部资源地交互。

/-
题外话：
我发现，这些证明根本不是“人看的”。杂一看就是天书，而且文字逻辑与通常的编程语言不一样，也不是普通的数学证明语言，它明显更抽象，更规则。

当我处在“解题”状态时，我能理解这些证明，但这种证明，既不是简单的数学语言，也不像编程语言。而是一种杂揉体。

理解这种语言，除了文本本身，还需要结合右侧面板的 goal。
这其实很像人类的工作模式，我们在证明时，头脑会保持一个 goal 进行指引。

---

我觉得吧，人类在做这类证明的时候，从来不是线性看文本的，怎么模拟思维背后的这个东西。就是说，怎么模拟头脑的模型，文本是和这个头脑模型一直交互的。这个例子中，头脑模型就是一个证明目标。

包括，哪怕我们人去看这个证明，也不是线性地往下看，不是单纯地上下文。
一个想法：使用一个杂揉体，比如 -文本-思维状态-文本-... 不断地交互
p.s. 此时，突然觉得自己对 AI 理解太浅，需要的时候不能灵活定制。。。
-/

/-
Let's see how backward reasoning would look like here.
As usual with this style, we use `apply` and enjoy Lean specializing assumptions for us
using so-called unification.
-/

/-
题外话的题外话：你觉得不是“人看的”，那是因为你的掌握熟练程度不够，训练不够。照你怎么说，编程代码也”不是人看的“
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- We need to prove (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Since g is non-decreasing, it suffices to prove f x₁ ≤ f x₂
  unfold non_decreasing at hf hg
  apply hg
  -- which follows from our assumption on f
  apply hf
  -- and on x₁ and x₂
  exact h
}

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by {
  intro x₁ x₂ h
  apply hg
  apply hf
  exact h
}

/- # Finding lemmas

Lean's mathematical library contains many useful facts,
and remembering all of them by name is infeasible.
The following exercises teach you two such techniques.
* `simp` will simplify complicated expressions.
* `apply?` will find lemmas from the library.
-/

/- Use `simp` to prove the following. Note that `X : Set ℝ`
means that `X` is a set containing (only) real numbers. -/
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by {
   simp
   exact hx
}

/- Use `apply?` to find the lemma that every continuous function with compact support
has a global minimum. -/

example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by {
  exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f

}

/-
This is the end of this file where you learned how to handle universal quantifiers.
You learned about tactics:
* `unfold`
* `specialize`
* `simp`
* `apply?`

You now have a choice what to do next. There is one more basic file `04Exists`
about the existential quantifier and conjunctions. You can do that now,
or dive directly in one of the specialized files.
In the latter case, you should come back to `04Exists` if you get stuck on anything with `∃`/`∧`.

You can start with specialized files in the `Topics` folder. You have choice between
* `ClassicalPropositionalLogic` (easier, logic) if you want to learn
  how to do classical propositional logic in Lean.
* `IntuitionisticPropositionalLogic` (harder, logic) if you want a bigger challenge
  and do intuitionistic propositional logic.
* `SequenceLimit` (easier, math) if you want to do some elementary calculus.
  For this file it is recommended to do `04Exists` first.
* `GaloisAjunctions` (harder, math) if you want some more abstraction
  and learn how to prove things about adjunctions between complete lattices.
  It ends with a constructor of the product topology and its universal property
  manipulating as few open sets as possible.
-/
