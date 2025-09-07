```lean
import GlimpseOfLean.Library.Basic

open PiNotation

```

# 抽象废话101：Galois 伴随

在这个文件中，我们将使用最简单的伴随例子：完备格之间的 Galois 连接。Lean 的数学库 Mathlib 中有很多关于这个主题的内容，但在这里我们将为了练习而构建我们自己的版本。这个文件构建了这些对象的基本理论，你在这个文件中证明的每个引理都被命名了，可以重复使用来证明后续的引理。

```lean
namespace Tutorial

section InfSup
variable [PartialOrder X]

```

在这一节中，`X` 是一个配备了偏序关系的类型。所以你可以使用以下引理：
* `le_rfl {a : X} : a ≤ a`
* `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`
* `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`

参数周围的花括号表示这些参数是隐式的，所以 Lean 永远不会要求它们，因为它们肯定可以从上下文中推断出来；特别是，当应用包含花括号中变量的引理时，你应该*不*提供相应的值。

我们还将使用集合 `s` 的下界集的定义：

`lowerBounds s = {x  | ∀ a ∈ s, x ≤ a}`

以及类似地

`upperBounds s = {x  | ∀ a ∈ s, a ≤ x}`

- 如果 `X` 中的每个元素是集合 `s` 的下界当且仅当它在 `x₀` 下方，则元素 `x₀` 是 `X` 中集合 `s` 的下确界。

```lean
def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by
  -- sorry
  rw [h]
  -- Slower alternative:
  -- specialize h x₀
  -- apply h.2
  -- apply le_rfl
  -- sorry

```

- 一个集合最多有一个下确界。

```lean
def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by
  -- sorry
  apply le_antisymm
  · exact (hx₁ x₀).1 (isInf.lowerBound hx₀)
    -- Slower alternative:
    -- apply (hx₁ x₀).1
    -- apply isInf.lowerBound hx₀
  · exact (hx₀ x₁).1 (isInf.lowerBound hx₁)
  -- sorry

```

- 如果 `X` 中的每个元素是集合 `s` 的上界当且仅当 `x₀` 在它下方，则元素 `x₀` 是 `X` 中集合 `s` 的上确界。

```lean
def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x

```

下一个引理通过将 `isInf.lowerBound` 应用到配备相反序关系的 `X` 来证明。你不需要准确理解这是如何实现的，因为会提供所有使用这个技巧的证明。

```lean
lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h

```

- 一个集合最多有一个上确界。

```lean
lemma isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁

```

- 如果一个从 `Set X` 到 `X` 的函数将每个集合发送到该集合的下确界，则它是一个下确界函数。

```lean
def isInfFun (I : Set X → X) :=
  ∀ s : Set X, isInf s (I s)

```

- 如果一个从 `Set X` 到 `X` 的函数将每个集合发送到该集合的上确界，则它是一个上确界函数。

```lean
def isSupFun (S : Set X → X) :=
  ∀ s : Set X, isSup s (S s)

```

下一个引理是这个文件中的第一个关键结果。如果 `X` 承认一个下确界函数，那么它自动承认一个上确界函数。

```lean
lemma isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by
  -- sorry
  intro s x
  constructor
  · intro hx
    exact (h _).lowerBound hx
  · intros hx y hy
    calc
      y ≤ I (upperBounds s) := (h _ y).mp (fun z hz ↦ hz hy)
      _ ≤ x                 := hx
  -- sorry

```

当然，我们也有从上确界函数构造下确界函数的对偶结果。

```lean
lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h

```

我们现在准备好了这个文件的第一个主要定义：完备格。

- 一个完备格是一个配备了偏序、下确界函数和上确界函数的类型。例如，`X = Set Y` 配备包含序、交集函数和并集函数是一个完备格。特别是，这里的 "lattice" here has nothing to do with lattices as discrete subgroups in Euclidean spaces.

```lean
class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S

```

- 将一个完备格 `X` 转换为对偶格。当使用上面的 `OrderDual` 技巧时，Lean 将自动选取这个构造。

```lean
instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)

```

我们现在可以使用上面的第一个主要结果来从偏序类型上的下确界或上确界函数构建一个完备格。

- 从偏序类型上的下确界函数构建完备格结构。

```lean
def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h

```

- 从偏序类型上的上确界函数构建完备格结构。

```lean
def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h

```

直到本节的结尾，`X` 都将是一个完备格。

```lean
variable [CompleteLattice X]

```

- 完备格上的下确界函数。

```lean
notation "Inf" => CompleteLattice.I

```

- 完备格上的上确界函数。

```lean
notation "Sup" => CompleteLattice.S

```

我们现在以完备格的形式重新表述上面证明的几个引理。

```lean
lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound

```

我们现在证明一系列引理，断言 `Inf`（然后由对偶性 `Sup`）按照你的直觉行为。如果你认为你能够证明它们并且想看更有趣的东西，你可以自由地跳过它们转到伴随节。

在下面的第一个引理中，你可能想使用 `lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s` 或者作为你证明的一部分重新证明它。

```lean
lemma Inf_pair {x x' : X} : x ≤ x' ↔ Inf {x, x'} = x := by
  -- sorry
  constructor
  · intro h
    apply (CompleteLattice.I_isInf _).eq
    intro z
    constructor
    · intro hz
      apply hz
      simp
    · intro hz
      simp
      constructor
      · apply hz
      · calc z ≤ x  := by apply hz -- or simply `:= hz`
             _ ≤ x' := by apply h -- or simply `:= h`
  · intro h
    calc
      x = Inf {x, x'} := by rw [h]
      _ ≤ x' := by apply lowerBound_Inf; simp
  -- sorry

lemma Sup_pair {x x' : X} : x ≤ x' ↔ Sup {x, x'} = x' := by
  rw [Set.pair_comm x x']
  exact Inf_pair (X := OrderDual X)

```

让我们证明 `Set` 形成一个完备格。

```lean
lemma isInfInter {Y : Type} (S : Set (Set Y)) : isInf S (⋂₀ S) := by
  -- sorry
  intro t
  constructor
  · intro ht x hx u hu
    exact ht hu hx
  · intro ht u hu x hx
    exact ht hx _ hu
  -- sorry

lemma isSupUnion {Y : Type} (S : Set (Set Y)) : isSup S (⋃₀ S) := by
  -- sorry
  intro t
  constructor
  · intro ht x hx
    rcases hx with ⟨s, hs, hx⟩
    exact ht hs hx
  · intro ht u hu x hx
    apply ht
    use u
  -- sorry

instance {Y : Type} : CompleteLattice (Set Y) where
  I := Set.sInter
  I_isInf := fun S ↦ isInfInter S
  S := Set.sUnion
  S_isSup := fun S ↦ isSupUnion S

end InfSup

section Adjunction
```

我们现在准备好了这个文件的第二个中心定义：有序类型之间的伴随。

- 有序类型之间的一对函数 `l` 和 `r` 是伴随的，如果 `∀ x y, l x ≤ y ↔ x ≤ r y`。人们也说它们形成一个 Galois 连接。这里 `l` 代表"左"，`r` 代表"右"。

```lean
def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y

```

你需要记住的例子是直接像和逆像之间的伴随。给定 `f : α → β`，我们有：
* `Set.image f : Set α → Set β` 记作 `f ''`
* `Set.preimage f : Set β → Set α` 记作 `f ⁻¹'`

```lean
lemma image_preimage_adjunction {α β : Type} (f : α → β) :
    adjunction (Set.image f) (Set.preimage f) := by
  intros s t
  exact Set.image_subset_iff

lemma adjunction.dual [PartialOrder X] [PartialOrder Y] {l : X → Y} {r : Y → X}
    (h : adjunction l r) :
    adjunction (X := OrderDual Y) (Y := OrderDual X) r l := by
  -- sorry
  intros y x
  constructor
  exact (h x y).2
  exact (h x y).1
  -- sorry

```

在这一节的剩余部分，`X` 和 `Y` 是完备格。

```lean
variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]

```

我们现在迎来这个文件的第二个主要定理：完备格的伴随函子定理。这个定理说完备格之间的函数是左伴随（或右伴随）当且仅当它与 `Sup`（或与 `Inf`）交换。

我们首先定义候选的右伴随（不对原始映射做任何假设）。

- 为完备格之间的映射构造一个候选的右伴随。如果映射与 `Sup` 交换，这是一个真正的伴随，参见 `adjunction_of_Sup`。

```lean
def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}

```

下面定理的证明不长，但也不是完全显而易见的。首先你需要理解陈述中的记号。`l '' s` 是 `s` 在 `l` 下的直接像。这个 `''` 是 `Set.image` 的记号。将你的光标放在这个记号上并使用上下文菜单"跳转到定义"将带你到定义 `Set.image` 并包含关于它的大量引理的文件。在参考解决方案中使用的那些是：

* `Set.image_pair : (f : α → β) (a b : α) : f '' {a, b} = {f a, f b}`
* `Set.image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s`

证明提示：一个方向很容易，不使用关键假设。对于另一个方向，你可能应该首先证明 `Monotone l`，即 `∀ ⦃a b⦄, a ≤ b → l a ≤ l b`，然后证明对于每个 `y`，`Sup (l '' { x | l x ≤ y }) ≤ y`。

```lean
theorem adjunction_of_Sup {l : X → Y} (h : ∀ s : Set X, l (Sup s) = Sup (l '' s)) :
    adjunction l (mk_right l) := by
  -- sorry
  intro x y
  constructor
  · intro h'
    exact (CompleteLattice.S_isSup {x | l x ≤ y}).upperBound h'
  · intro h'
    have l_mono : Monotone l := by
      intro a b hab
      have := h {a, b}
      rw [Sup_pair.1 hab, Set.image_pair] at this
      exact Sup_pair.2 this.symm
    have Sup_le_y : Sup (l '' { x | l x ≤ y }) ≤ y := by
      apply (CompleteLattice.S_isSup (l '' { x | l x ≤ y }) y).1
      intro y' hy'
      rcases hy' with ⟨x, hx, hxy'⟩
      rw [← hxy']
      apply hx
    calc
      l x ≤ l (mk_right l y) := l_mono h'
      _   = Sup (l '' { x | l x ≤ y }) := h {x | l x ≤ y}
      _   ≤ y := Sup_le_y
  -- sorry

```

当然，我们也可以玩同样的游戏来构造左伴随。

- 为完备格之间的映射构造一个候选的左伴随。如果映射与 `Inf` 交换，这是一个真正的伴随，参见 `adjunction_of_Inf`。

```lean
def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

theorem adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology
```

在这一节中，我们将上面开发的理论应用到点集拓扑。我们的第一个目标是为给定类型上的拓扑类型 `Topology X` 配备完备格结构。然后我们将任何映射 `f : X → Y` 转换为 `Topology X` 和 `Topology Y` 之间的伴随 `(f⁎, f ^*)` 并用它来构建乘积拓扑。当然 mathlib 知道这一切，但我们将继续构建我们自己的理论。

```lean
@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_iUnion : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_iInter : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)

```

让我们对我们的定义进行两个快速的合理性检查，因为许多教科书在拓扑空间的定义中包含冗余条件。

```lean
lemma isOpen_empty (T : Topology X) : T.isOpen ∅ := by
  have : (∅ : Set X) = ⋃ i : Empty, i.rec := by
    rw [Set.iUnion_of_empty]
  rw [this]
  exact T.isOpen_iUnion Empty.rec

lemma isOpen_univ (T : Topology X) : T.isOpen Set.univ := by
  have : (Set.univ : Set X) = ⋂ i : Empty, i.rec := by
    rw [Set.iInter_of_empty]
  rw [this]
  exact T.isOpen_iInter  Empty.rec (Finite.of_fintype Empty)

```

定义 `Topology` 上的 `ext` 属性告诉 Lean 自动构建以下扩展性引理：`Topology.ext_iff (T T' : Topology X), T = T' ↔ x.isOpen = y.isOpen` 它还为 `ext` 策略注册这个引理使用（我们将在下面回到这个）。

- 我们使用对偶于 `Set (Set X)` 诱导的序的序来排序 `Topology X`。选择这种方法有很好的理由，但超出了本教程的范围。

```lean
instance : PartialOrder (Topology X) :=
PartialOrder.lift (β := OrderDual $ Set (Set X)) Topology.isOpen (fun _ _ ↦ (Topology.ext_iff).2)

```

- `Topology X` 上的上确界函数。

```lean
def SupTop (s : Set (Topology X)) : Topology X where
  isOpen := fun V ↦ ∀ T ∈ s, T.isOpen V
  isOpen_iUnion := by
    intros ι t ht a ha
    exact a.isOpen_iUnion fun i ↦ ht i a ha

  isOpen_iInter := by
    intros ι t ht hι a ha
    exact a.isOpen_iInter (fun i ↦ ht i a ha) hι

```

由于上面的上确界函数来自 `OrderDual (Set (Set X))` 的上确界函数，它确实是一个上确界函数。我们可以陈述一个抽象引理说这一点，但这里直接证明同样简单并且很有趣。

```lean
lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) :=
fun _ _ ↦ ⟨fun hT _ hV _ hs ↦ hT hs hV, fun hT T' hT' _ hV ↦ hT hV T' hT'⟩

```

我们可以使用我们的抽象理论免费获得下确界函数，因此在 `Topology X` 上获得完备格结构。请注意，我们的抽象理论确实在做非平凡的工作：下确界函数不是来自 `OrderDual (Set (Set X))`。

```lean
instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop

```

让我们在完备格记号中重新表述我们的 `Sup` 构造是什么。证明简单地说"这是定义上真实的"。

```lean
lemma isOpen_Sup {s : Set (Topology X)} {V : Set X} : (Sup s).isOpen V ↔ ∀ T ∈ s, T.isOpen V :=
  Iff.rfl

```

我们现在开始构建由任何映射 `f : X → Y` 诱导的 `Topology X` 和 `Topology Y` 之间的伴随。我们将手动构建左伴随，然后调用我们的伴随函子定理。

```lean
def push (f : X → Y) (T : Topology X) : Topology Y where
  isOpen := fun V ↦ T.isOpen (f ⁻¹' V)
  isOpen_iUnion := by
    -- sorry
    intros ι s hs
    rw [Set.preimage_iUnion]
    exact T.isOpen_iUnion hs
    -- sorry

  isOpen_iInter := by
    -- sorry
    intros ι s hs hι
    rw [Set.preimage_iInter]
    exact T.isOpen_iInter hs hι
    -- sorry

postfix:1024 "⁎" => push -- type using `\_*`

```

- 对于拓扑 `T` 和 `T'`，映射 `f : X → Y` 是连续的，如果每个开集的逆像都是开集。

```lean
def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) :=  f ⁎ T ≤ T'

```

让我们检查定义确实在说我们声称它说的话。

```lean
example (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl

```

注意下面的证明如何使用 `ext` 策略，由于在 `Topology` 定义上的 `ext` 属性，它知道两个拓扑相等当且仅当它们有相同的开集。

```lean
lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    g ⁎ (f ⁎ T) = (g ∘ f) ⁎ T := by
  ext V
  exact Iff.rfl

```

我们想要 `f ⁎` 的右伴随，所以我们需要检查它与 `Sup` 交换。你可能想使用 `Set.ball_image_iff : (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x)` 其中 "ball" 代表 "bounded for all"，即 `∀ x ∈ ...`。

```lean
lemma push_Sup (f : X → Y) {t : Set (Topology X)} : f ⁎ (Sup t) = Sup (f ⁎ '' t) := by
  -- sorry
  ext V
  rw [isOpen_Sup, Set.forall_mem_image]
  exact Iff.rfl
  -- sorry

def pull (f : X → Y) (T : Topology Y) : Topology X := mk_right (push f) T

postfix:1024 "^*" => pull

def ProductTopology {ι : Type} {X : ι → Type} (T : Π i, Topology (X i)) : Topology (Π i, X i) :=
Inf (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i)))

lemma ContinuousProductTopIff {ι : Type} {X : ι → Type} (T : Π i, Topology (X i))
  {Z : Type} (TZ : Topology Z) {f : Z → Π i, X i}:
    Continuous TZ (ProductTopology T) f ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i) := by
  -- sorry
  calc
    Continuous TZ (ProductTopology T) f
    _ ↔ f ⁎ TZ ∈ lowerBounds (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i))) := by
          rw [CompleteLattice.I_isInf]
          exact Iff.rfl

    _ ↔ ∀ i, f ⁎ TZ ≤ (fun x ↦ x i) ^* (T i)        := by rw [lowerBounds_range]
    _ ↔ ∀ i, (fun x ↦ x i) ⁎ (f ⁎ TZ) ≤ T i        := by
          apply forall_congr'
          intro i
          rw [pull, ← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]

    _ ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i)  := Iff.rfl
```

unfold Continuous ProductTopology
  rw [← CompleteLattice.I_isInf, lowerBounds_range]
  apply forall_congr'
  intro i
  unfold pull
  rw [← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]
rfl

```lean
  -- sorry

end Topology

namespace Subgroups

@[ext]
structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ ⦃x y : G⦄, x ∈ carrier → y ∈ carrier → x*y ∈ carrier
  inv_mem : ∀ ⦃x : G⦄, x ∈ carrier → x⁻¹ ∈ carrier

instance [Group G] : Membership G (Subgroup G) := ⟨fun H x ↦ x ∈ H.carrier⟩

variable {G : Type} [Group G]

instance : PartialOrder (Subgroup G) :=
  PartialOrder.lift Subgroup.carrier (fun _ _ ↦ (Subgroup.ext_iff).2)

```

一个子群的交集是一个子群。

```lean
def SubgroupInf (s : Set (Subgroup G)) : Subgroup G where
  carrier := ⋂ H ∈ s, H.carrier
  one_mem := by
    -- sorry
    rw [Set.mem_iInter₂]
    intro H _
    exact H.one_mem
    -- sorry

  mul_mem := by
    -- sorry
    intro x y hx hy
    rw [Set.mem_iInter₂] at hx hy ⊢
    intro H hH
    exact H.mul_mem (hx H hH) (hy H hH)
    -- sorry

  inv_mem := by
    -- sorry
    intro x hx
    rw [Set.mem_iInter₂] at hx ⊢
    intro H hH
    exact H.inv_mem (hx H hH)
    -- sorry


lemma SubgroupInf_carrier (s : Set (Subgroup G)) :
  (SubgroupInf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
by simp [SubgroupInf]
-- omit

lemma isInf.lift [PartialOrder X] {f : Y → X} (hf : Function.Injective f) {s : Set Y} {y : Y}
  (hy : isInf (f '' s) (f y)) : @isInf Y (PartialOrder.lift f hf) s y := by
  intro y'
  erw [← hy (f y')]
  constructor
  · intro hy' x hx
    rcases hx with ⟨y'', hy'', H⟩
    rw [← H]
    exact hy' hy''
  · intro hy' y'' hy''
    apply hy'
    exact Set.mem_image_of_mem f hy''

-- omit
lemma SubgroupInf_is_Inf : isInfFun (SubgroupInf : Set (Subgroup G) → Subgroup G) := by
  -- sorry
  intro s H
  apply isInf.lift (fun _ _ ↦ (Subgroup.ext_iff).2)
  rw [SubgroupInf_carrier]
  apply isInfInter
  -- sorry

instance : CompleteLattice (Subgroup G) := CompleteLattice.mk_of_Inf SubgroupInf_is_Inf

lemma Inf_carrier (s : Set (Subgroup G)) : (Inf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
  SubgroupInf_carrier s

def forget (H : Subgroup G) : Set G := H.carrier

def generate : Set G → Subgroup G := mk_left forget

lemma generate_forget_adjunction : adjunction (generate : Set G → Subgroup G) forget := by
  -- sorry
  exact adjunction_of_Inf SubgroupInf_carrier
  -- sorry

variable {G' : Type} [Group G']

def pull (f : G →* G') (H' : Subgroup G') : Subgroup G where
  carrier := f ⁻¹' H'.carrier
  one_mem := by
    -- sorry
    show f 1 ∈ H'
    rw [f.map_one]
    exact H'.one_mem
    -- sorry

  mul_mem := by
    -- sorry
    intro x y hx hy
    show f (x*y) ∈ H'
    rw [f.map_mul]
    exact H'.mul_mem hx hy
    -- sorry

  inv_mem := by
    -- sorry
    intro x hx
    show f x⁻¹ ∈ H'
    rw [f.map_inv]
    exact H'.inv_mem hx
    -- sorry


lemma pull_carrier (f : G →* G') (H' : Subgroup G') : (pull f H').carrier = f ⁻¹' H'.carrier :=
  rfl

```

让我们真正懒惰，通过伴随定义子群推进。

```lean
def push (f : G →* G') : Subgroup G → Subgroup G' := mk_left (pull f)

lemma push_pull_adjunction (f : G →* G') : adjunction (push f) (pull f) := by
  -- sorry
  apply adjunction_of_Inf
  intro S
  ext x
  simp [Inf_carrier, Set.image_image, pull, Set.preimage_iInter]
  -- sorry

end Subgroups

section
```

我们的下一个具体目标是 `push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S)`

这将需要几个更抽象的引理。

```lean
variable {X : Type} [PartialOrder X]
         {Y : Type} [PartialOrder Y]

lemma unique_left {l l' : X → Y} {r : Y → X} (h : adjunction l r) (h' : adjunction l' r) :
    l = l' := by
  -- sorry
  ext x
  apply le_antisymm
  · rw [h, ← h']
  · rw [h', ← h]
  -- sorry

lemma unique_right {l : X → Y} {r r' : Y → X} (h : adjunction l r) (h' : adjunction l r') :
    r = r' := by
  -- sorry
  exact (unique_left h'.dual h.dual).symm
  -- sorry

variable {Z : Type} [PartialOrder Z]

lemma adjunction.compose {l : X → Y} {r : Y → X} (h : adjunction l r)
  {l' : Y → Z} {r' : Z → Y} (h' : adjunction l' r') : adjunction (l' ∘ l) (r ∘ r') := by
  -- sorry
  intro x z
  rw [Function.comp_apply, h', h]
  rfl
  -- sorry

-- omit
lemma left_comm_of_right_comm {W : Type} [PartialOrder W] [CompleteLattice W]
    {lYX : X → Y} {uXY : Y → X} (hXY : adjunction lYX uXY)
    {lWZ : Z → W} {uZW : W → Z} (hZW : adjunction lWZ uZW)
    {lWY : Y → W} {uYW : W → Y} (hWY : adjunction lWY uYW)
    {lZX : X → Z} {uXZ : Z → X} (hXZ : adjunction lZX uXZ)
    (h : uXZ ∘ uZW = uXY ∘ uYW) : lWZ ∘ lZX = lWY ∘ lYX := by
  have A₁ := hXZ.compose hZW
  rw [h] at A₁
  exact unique_left A₁ (hXY.compose hWY)
-- omit

end

namespace Subgroups
variable {G : Type} [Group G] {G' : Type} [Group G']

```

作为最后的挑战，我们提出以下引理。

- 群同态下某个集合 `S` 生成的子群的像是由 `S` 的像生成的。

```lean
lemma push_generate (f : G →* G') : push f ∘ generate = generate ∘ (Set.image f) := by
  -- sorry
  apply left_comm_of_right_comm
  apply image_preimage_adjunction
  apply push_pull_adjunction
  apply generate_forget_adjunction
  apply generate_forget_adjunction
  ext H
  exact Iff.rfl
  -- sorry

end Subgroups
end Tutorial

```