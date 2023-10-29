```lean
import GlimpseOfLean.Library.Basic
```

在这个文件中，我们将操控实数序列的基本极限定义。
尽管 mathlib 对极限有更通用的定义，但在这里，
我们希望练习使用在之前文件中介绍的逻辑运算符和关系。

在我们开始之前，让我们确保 Lean 不需要太多的帮助来证明等式或不等式，这些等式或不等式是从已知的等式和不等式中线性地得出的。这是线性算术策略：`linarith` 的任务。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith
```

让我们使用 `linarith` 来证明一些练习。

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  sorry
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  sorry
}
```

一个序列`u`是从`ℕ`到`ℝ`的函数，因此 Lean 表述
`u : ℕ → ℝ`
我们将使用的定义是：

-- “u 趋向于 l”的定义
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

注意 `∀ ε > 0, _`的使用是
`∀ ε, ε > 0 → _ `的缩写

特别的，像`h : ∀ ε > 0, _` 这样的陈述
可以被专门化为一个给定的 `ε₀` 通过
  `specialize h ε₀ hε₀`
其中 `hε₀` 是 `ε₀ > 0` 的证明。

另外注意，无论何时 Lean 都期望一些证明算式，我们可以
使用关键词 `by` 开始一个策略模式证明。
例如，如果局部上下文包含：

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

然后我们可以使用以下方法将 h 特化到实数 δ/2：
  `specialize h (δ/2) (by linarith)`
其中 `by linarith` 将提供 Lean 所期望的 `δ/2 > 0` 的证明。

如果 u 是一个常数，其值为 l， 那么 u 会趋近于 l。
提示：`simp` 可以将 `|1 - 1|` 重写为 `0`

```lean
example (h : ∀ n, u n = l) : seq_limit u l := by {
  sorry
}
```

在处理绝对值时，我们将使用引理：

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

我们还将使用三角形不等式的变体

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
或者
`abs_sub_le (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
或它的倒数版本：
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`

```lean
-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  sorry
}
```

当处理 max 时，你可以使用

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

让我们来看一个例子。

```lean
-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2
  · exact hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2
  · exact hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}
```

让我们做一些类似的事情：夹逼定理。

```lean
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  sorry
}
```

在下一个练习中，我们将使用

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

回忆一下我们在文件开头列出的三种三角不等式的变形。

```lean
-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  sorry
}
```

让我们在进行证明之前先来一起解读定义。

```lean
def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  sorry
}
```

我们现在将研究子序列。

我们将使用的新定义是，如果 `φ : ℕ → ℕ` 是 (严格) 递增的，那么它就是一个提取。

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

接下来，`φ` 将总是表示一个从 `ℕ` 到 `ℕ` 的函数。

接下来的引理可以通过简单的归纳法进行证明，但是我们在这个教程中还没有看到归纳法。如果你做了自然数游戏，那么你可以删除下面的证明并尝试重建它。

一个提取函数大于 id

```lean
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}
```

在这个练习中，我们使用 `∃ n ≥ N, ...` ，这是 `∃ n, n ≥ N ∧ ...` 的缩写。

提取会对任意大的输入取任意大的值。

```lean
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  sorry
}
```

一个实数 `a` 是一个序列 `u` 的聚点，
如果 `u` 有一个子序列收敛于 `a`。

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`

如果 `a` 是 `u` 的聚点，那么对于任意大的输入，都存在接近 `a` 的 `u` 值。

```lean
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  sorry
}
```

如果 `u` 趋向于 `l`，那么它的子序列也将趋向于 `l`。

```lean
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  sorry
}
```

如果 `u` 趋向于 `l`，那么它的所有聚点都等于 `l`。

```lean
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  sorry
}
```

\# Cauchy序列 

在数学中，一个 *Cauchy序列* 是一个能够满足特定（给定任意大于0的正数，总存在一对序列中的项，他们的距离小于给定正数）的序列。

对于所有的实数ε > 0 ，存在一个正的整数N，如果n 和 m 都大于N，那么 |a_n - a_m| < ε。

这可以解释为，对于任何小的正距离，都有一个点从那里开始的序列，剩余部分都在这个距离内。

如果空间是 *完备的* ，那么 Cauchy 序列包含一个极限。例如，实数线或复数平面是完备的， Cauchy 序列是如果它们收敛的序列，他们的极限属于相同的空间。然而，并不是所有的空间都是完备的。Cauchy 序列的一个重要类别是所有典型计算的序列——它们收敛到代数或者**瞬态**式子的解。

许多编程语言对实数和复数的准确表示实施了严格的限制，这可能制约某些计算的准确性。在这些情况下，我们可以使用 Cauchy 序列来表示和计算复数或实数的精确值。

*Lean* 程序库提供了多种方法来表示和操作 Cauchy 序列，为精确的数值计算提供解决方案。它还支持一种叫做 *formal topologies* 的抽象数理，该理论提供了一个框架，使对那些不能直接用公理表示的空间的实现成为可能。

```lean
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  sorry
}
```

在接下来的练习中，你可以重复使用 
 near_cluster： cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε

```lean
example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  sorry
```
