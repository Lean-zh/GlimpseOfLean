```lean
import GlimpseOfLean.Library.Ring

setup
open PiNotation BigOperators Function Classical
noncomputable section

namespace GlimpseOfLean

```

# 交换环及其商环

这个文件是环论所需对象的一次巡礼：环、环同态和同构、理想和商环。第一部分完全是基础的，仅使用交换环的定义。中间部分介绍了环对理想的商环，并以诺特第一同构定理的证明为高潮。最后部分使用理想的算术，并以中国剩余定理的证明为高潮。

```lean
open RingHom Function

```

要说"设 `R` 为任意交换环"，我们写 `{R : Type*} [CommRing R]` 来声明一个类型 `R`，然后假设它装备了交换环结构。

现在，给定元素 `x y z : R`，我们可以对环的元素应用环运算符，如 `+`、`-`、`*`、`0` 和 `1` 来获得新元素。`ring` 策略可以化简得到的表达式。

（这里，`2` 是 `1 + 1` 的缩写，`3` 是 `1 + 1 + 1`，...）

```lean
example {R : Type*} [CommRing R] (x y z : R) :
    x * (y + z) + y * (z + x) + z * (x + y) = 2 * x * y + 2 * y * z + 2 * x * z := by
  ring

```

## 同态和同构

给定环 `R` 和环 `S`，从 `R` 到 `S` 的环同态写作 `f : R →+* S`。像函数一样，我们可以通过写 `f x` 将同态 `f` 应用到元素 `x : R` 上。`simp` 策略知道关于环同态的基本事实。例如，它们保持运算 `+`、`*`、`0` 和 `1`。

```lean
section homomorphisms
variable {R S : Type*} [CommRing R] [CommRing S]


example (f : R →+* S) (x y : R) :
    f (1 + x * y) + f 0 = 1 + f x * f y := by
  simp

variable {T : Type*} [CommRing T]
```

让我们试着定义两个环同态的复合。我们必须提供映射的定义，然后证明它尊重环结构。当然 Mathlib 已经有了这个，但我们重新做这个练习。

尝试使用 `intro` 和 `simp` 填入下面的 `sorry`。

```lean
def RingHom.comp (g : S →+* T) (f : R →+* S) : R →+* T where
  toFun x := g (f x)
  map_one' := by
    sorry
  map_mul' := by
    sorry
  map_zero' := by
    sorry
  map_add' := by
    sorry

```

`R` 和 `S` 之间的环同构写作 `e : R ≃+* S`。我们可以通过写 `e x` 将 `e` 作为从 `R` 到 `S` 的函数，其中 `x : R`。要在另一个方向上应用 `e`，从 `S` 到 `R`，我们写 `e.symm y`，其中 `y : S`。

要直接定义环同构，我们必须提供两个映射：`toFun : R → S` 和 `invFun : S → R`，并证明它们互为逆映射，此外还要证明加法和乘法被保持。我们将在下面看到一个不显式提供逆态射的例子。尝试证明两个同构的复合仍然是同构。

提示：`Function.LeftInverse` 和 `Function.RightInverse` 是全称量词陈述。尝试展开它们或使用 `intro x` 来推进。

```lean
def RingEquiv.comp (g : S ≃+* T) (f : R ≃+* S) : R ≃+* T where
  toFun x := g (f x)
  invFun x := f.symm (g.symm x)
  left_inv := by
    sorry
  right_inv := by
    sorry
  map_add' := by
    sorry
  map_mul' := by
    sorry

end homomorphisms

```

## 理想和理想商环

环 `R` 中的理想在 Mathlib 中写作 `I : Ideal R`。对于环的元素 `x : R`，我们可以通过写 `x ∈ I` 来断言 `x` 在理想 `I` 中。

不幸的是，我们不能依赖 `simp` 来证明理想的成员关系。策略 `aesop` 进行强大的（但较慢的）搜索，通过更多的事实。

```lean
variable {R} [CommRing R]

example (I : Ideal R) (x y : R) (hx : x ∈ I) : y * x + x * y - 0 ∈ I := by
  aesop

```

一个重要的理想是环同态的核。我们可以写作 `ker f : Ideal R`，其中 `f : R →+* S`。核定义为包含所有被 `f` 映射到 `0` 的元素：

```lean
example {S} [CommRing S] (f : R →+* S) (x : R) : x ∈ ker f ↔ f x = 0 := by
  rw [mem_ker]

```

要定义理想，我们给出载体集合的定义，然后证明它在左乘下封闭（因此也在右乘下封闭，因为我们这里的环是交换的）。

尝试证明两个理想的交集仍然是理想（当然 Mathlib 已经知道这个，这只是一个练习）。

```lean
def Ideal.inter (I J : Ideal R) : Ideal R where
  carrier := I ∩ J
  add_mem' := by
    sorry
  zero_mem' := by
    sorry
  smul_mem' := by
    sorry

```

最后，让我们看看理想商环。如果 `I` 是环 `R` 的理想，那么我们将 `R` 模 `I` 的商环写作 `R ⧸ I`。（这不是除法符号！输入 `\/` 来写商环符号。）商环又是一个环，我们可以像上面的 `R`、`S`、`T` 一样处理它，通过取商环的元素并将它们相加和相乘：

```lean
example (I : Ideal R) (x y z : R ⧸ I) :
    x * (y + z) + y * (z + x) + z * (x + y) = 2 * x * y + 2 * y * z + 2 * x * z := by
  ring

```

涉及商环有两个重要的同态。首先，从 `R` 到商环 `R ⧸ I` 的标准映射，称为 `Ideal.Quotient.mk I : R →+* R ⧸ I`。

当两个 `R` 的元素的差在理想中时，它们被映射到商环中的同一个元素：

```lean
example (I : Ideal R) (x y : R) (h : x - y ∈ I) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact h

```

我们可以更简洁地说：`Ideal.Quotient.mk I` 的核恰好是 `I`。

```lean
example (I : Ideal R) : ker (Ideal.Quotient.mk I) = I :=
  Ideal.mk_ker

```

商环 `R⧸I` 和同态 `Ideal.Quotient.mk I` 构成了"最小"的环和从 `R` 在 `I` 上消失的同态对：任何其他这样的同态都通过它分解。这是 `R⧸I` 的泛性质。分解的同态是 `Ideal.Quotient.lift I f hfI : R ⧸ I →+* S` 其中 `f : R →+* S` 且 `hfI : ∀ a ∈ I, f a = 0`。

这给了我们开始证明第一同构定理所需的最后成分。首先，我们将证明任何同态 `f : R →+* S` 作为映射 `R ⧸ ker f →+* S` 是良定义的。

尝试使用 `intro`、`rw`、`apply` 和/或 `exact` 填入缺失的证明。

```lean
section universal_property
variable {S} [CommRing S]

def kerLift (f : R →+* S) : R ⧸ ker f →+* S :=
  Ideal.Quotient.lift (ker f) f fun x ↦ by
    sorry

```

在新定义之后，为其基本性质制作引理是个好主意。

```lean
theorem kerLift_mk (f : R →+* S) (x : R) : kerLift f (Ideal.Quotient.mk (ker f) x) = f x := by
  sorry

```

当我们给定商环元素 `x : R ⧸ I` 时，为这个商环元素选择代表元 `x' : R` 通常是有用的证明步骤。`x' : R` 是 `x : R ⧸ I` 的代表元的陈述写作 `Ideal.Quotient.mk I x' = x`。每个 `x : R ⧸ I` 都有代表元的事实可以写作 `∃ x', Ideal.Quotient.mk I x' = x`。回忆 `04Exists.lean` 中 `Function.Surjective` 的定义，我们可以看到 `∃ x', Ideal.Quotient.mk I x' = x` 与 `Function.Surjective (Ideal.Quotient.mk I)` 相同，它在 Mathlib 中作为定理 `Ideal.Quotient.mk_surjective` 可用。

举个例子，让我们开始证明 `kerLift` 是单射的。我们首先使用 `Ideal.Quotient.mk_surjective` 为 `x` 选择代表元 `x'`。然后我们处处用 `Ideal.Quotient.mk I x'` 替换 `x`。

尝试完成证明。这里有一些有用的引理：`Ideal.Quotient.eq_zero_iff_mem`、`kerLift_mk`、`mem_ker`。

```lean
theorem kerLift_injective' (f : R →+* S) (x : R ⧸ ker f) (hx : kerLift f x = 0) : x = 0 := by
  rcases Ideal.Quotient.mk_surjective x with ⟨x', hx'⟩
  rw [← hx']
  rw [← hx'] at hx
  sorry

```

让我们使用 `Function.Injective` 重新陈述这个结果。

```lean
theorem kerLift_injective (f : R →+* S) : Injective (kerLift f) := by
  rw [injective_iff_map_eq_zero]
  exact kerLift_injective' f

```

## 第一同构定理

我们有了证明第一同构定理形式的所有成分：如果 `f : R →+* S` 是满射环同态，`R ⧸ ker f` 与 `S` 同构，通过我们将在下面定义的显式同构。要给出逆函数，我们使用定义 `surjInv`，它给出满射函数 `f` 的任意右逆（如果 `hf` 是 `f` 满射的证明，`surjInv` 是右逆的证明叫做 `rightInverse_surjInv hf`）。

```lean
def firstIsomorphismTheorem (f : R →+* S) (hf : Function.Surjective f) :
    R ⧸ ker f ≃+* S :=
  { toFun := kerLift f
    invFun x := Ideal.Quotient.mk (ker f) (surjInv hf x)
    right_inv := rightInverse_surjInv hf
    map_mul' := by
      sorry
    map_add' := by
      sorry
    left_inv := by
      -- 这里是所有内容汇聚的地方。
      -- 尝试遵循这个证明草图：
      -- * 引入变量 `x : R ⧸ ker f`。
      -- * 为 `x` 选择代表元，就像我们在 `kerLift_injective'` 中做的那样。
      -- * 应用我们的定理 `kerLift_injective`。
      -- * 使用 `kerLift_mk` 反复重写 `kerLift _ (Ideal.Quotient.mk _ _)`。
      -- * 通过用 `rightInverse_surjInv` 重写来完成。
      sorry
    }

end universal_property
end GlimpseOfLean

```

## 理想的算术和中国剩余定理

我们现在将一窥更高级的理论，即交换环中理想的中国剩余定理。这是众所周知的整数基本版本的推广。

```lean
section chinese
open RingHom

namespace Ideal
-- 上面一行的一个效果是允许写 `Quotient` 而不是 `Ideal.Quotient`

section definition_and_injectivity
-- `R` 是我们的交换环。
variable {R} [CommRing R]

-- `I` 是我们的理想族，由类型 `ι` 参数化。
variable {ι : Type} (I : ι → Ideal R)

```

我们想创建一个从 `R` 对 `I i` 的交集的商环到商环 `R⧸(I i)` 的积的环同态。对每个 `i : ι`，我们有从 `R` 到 `R⧸(I i)` 的同态，即 `Quotient.mk (I i)`。将所有这些收集到从 `R` 到积 `Π i, (R ⧸ I i)` 的映射中是 `Pi.ringHom` 的工作。我们将需要关于这个 `Pi.ringHom` 的引理 `ker_Pi_Quotient_mk`。然后我们需要 `Ideal.lift` 通过 `R` 对交集 `⨅ i, I i` 的商环来分解这个。注意，根据你使用的字体，交集符号 `⨅` 和积 `Π` 可能很难区分。

```lean
def chineseMap  : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
  Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Quotient.mk (I i))
    (by sorry)

```

让我们记录这个映射在元素上作用的两种稍微不同的拼写，按定义。

```lean
lemma chineseMap_mk (x : R) : chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Quotient.mk (I i) x :=
  rfl

lemma chineseMap_mk' (x : R) (i : ι) : chineseMap I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
  rfl

```

这个映射总是单射的，对理想族没有任何假设。这是前一节单射性的变化。

```lean
lemma chineseMap_injective : Injective (chineseMap I) := by
  sorry
end definition_and_injectivity

```

相比之下，满射性需要一些假设。基本版本处理有限的成对互质整数族。在一般情况下，我们想使用有限的成对互质理想族。

在 `Ideal R` 上有交换半环结构。这听起来像奇异的代数结构，但它与你在 `ℕ` 上有的相同：它很像交换环，除了没有减法运算。两个理想 `I` 和 `J` 是互质的，如果 `I + J = 1` 其中 `1` 是 `Ideal R` 的单位，即包含 `R` 所有元素的理想。这个条件应用于 `ℤ` 的理想 `nℤ` 和 `mℤ` 互质的事实本质上是贝祖等式。在 `Ideal R` 上还有序关系，`1` 是顶元素 `⊤`。

中国剩余定理证明中的关键引理是下面这个，它通过对有限集合 `s` 的归纳来证明。这里有个有趣的点。在纸上你可能会说你通过对 `s` 的基数的归纳来证明它。你会在 `s` 上放某种顺序，仅仅是为了能够挑出"最后"一个元素。通常 `s` 会是 `{1, …, n}`，对某个自然数 `n`。在 Lean 中，我们简单地说 `s` 是有限集合，并应用归纳原理 `Finset.induction` 说，为了证明某个类型 `ι` 中所有有限集合的某个性质，足以证明空集的性质，并且假设某个集合 `s` 有这个性质，证明 `s ∪ {i}` 也有这个性质，对每个不在 `s` 中的 `i`。证明的结构在下面给出，所以你不必记住如何

并集 `s ∪ {i}` 拼写为 `insert i s`。关于这个运算的以下引理会有用：

```lean
#check Finset.mem_insert_of_mem

#check Finset.mem_insert_self

variable {R : Type*} [CommRing R] {ι : Type}

lemma coprime_iInf_of_coprime {I : Ideal R} {J : ι → Ideal R} {s : Finset ι} :
    (∀ j ∈ s, I + J j = 1) → I + (⨅ j ∈ s, J j) = 1 := by
  induction s using Finset.induction with
  | empty =>
      sorry
  | @insert i s _ hs =>
      intro h
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      sorry

```

我们现在准备证明中国剩余定理中的满射性。我们需要在有限类型 `ι` 上写和。对任何 `f : ι → R`，`f` 的值的和是 `∑ i, f i`。关于这个运算的有用引理包括 `map_sum`，它说同态与这种和交换，以及 `Finset.sum_univ_eq_single`，它允许在假设 `f` 仅对 `ι` 的单个元素非零的情况下重写这个和。

```lean
lemma chineseMap_surjective [Fintype ι] {I : ι → Ideal R} (hI : ∀ i j, i ≠ j → I i + I j = 1) :
    Surjective (chineseMap I) := by
  intro g
  -- 如果你比较调用前后的策略状态，`choose` 策略的作用应该很清楚。
  choose f hf using fun i ↦ Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, Quotient.mk (I i) e = 1 ∧ ∀ j, j ≠ i → Quotient.mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, I i + I j = 1 := by
      sorry
    sorry
  choose e he using key
  sorry

```

我们现在可以将所有内容放在一起得到中国剩余同构。

```lean
noncomputable def chineseIso [Fintype ι] (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → I i + I j = 1) :
   (R ⧸ ⨅ i, I i) ≃+* Π i, R ⧸ I i :=
{ Equiv.ofBijective _ ⟨chineseMap_injective I, chineseMap_surjective hI⟩, chineseMap I with }

end Ideal
end chinese


```