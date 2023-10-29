```lean
import GlimpseOfLean.Library.Basic
```

在这个文件中，我们处理的是实数序列极限的基础定义。  
mathlib 提供了一种更加通用的极限定义，但是在这里，我们想要利用前面文件中涉及的逻辑运算符和关系来进行实践。

在我们开始之前，让我们确保 Lean 在证明线性地从已知的等式和不等式中得出的等式和不等式时，不需要太多的帮助。这就是线性算术策略：`linarith`。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith
```

让我们使用 `linarith` 来证明一些练习。

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  -- sorry
  linarith
  -- sorry
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  -- sorry
  linarith
  -- sorry
}
```

一序列 `u` 是从 `ℕ` 到 `ℝ` 的函数，因此 Lean 表示为
`u : ℕ → ℝ`
我们将使用的定义是：

-- "u 趋向于 l" 的定义
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

注意 `∀ ε > 0, _` 的使用，这是
`∀ ε, ε > 0 → _ `的简写。

特别的，像 `h : ∀ ε > 0, _` 这样的陈述
可以特殊化到给定的 `ε₀`，以
  `specialize h ε₀ hε₀`
的形式，其中 `hε₀` 是 `ε₀ > 0` 的证明。

同样请注意，任何 Lean 期望得到一些证明项的地方，我们都可以
使用关键词 `by` 开启策略模式证明。
例如，如果局部上下文含有：

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

那么我们可以使用
  `specialize h (δ/2) (by linarith)`
将 h 特殊化为实数 δ/2，其中 `by linarith` 将提供 Lean 所期望的 `δ/2 > 0` 的证明。

如果 u 是常数，值为 l，那么 u 趋向于 l。
提示：`simp` 可以将 `|1 - 1|` 重写为 `0`

```lean
example (h : ∀ n, u n = l) : seq_limit u l := by {
  -- sorry
  intros ε ε_pos
  use 0
  intros n _
  rw [h]
  simp
  linarith
  -- sorry
}
```

在处理绝对值时，我们会使用以下引理：

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

我们还会用到三角不等式的变形：

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
或者：
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
再或者其带引号的版本：
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`

```lean
-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  -- sorry
  rcases h (l/2) (by linarith) with ⟨N, hN⟩
  use N
  intros n hn
  specialize hN n hn
  rw [abs_le] at hN
  linarith [hN]
  -- sorry
}
```

当处理 max 时，你可以使用

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

让我们看一个例子。

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
  -- omit
```

-- 不使用 `calc` 的另一种证明
  simp
  have : |u n + v n - (l + l')| = |(u n - l) + (v n - l')|
  · ring
  rw [this]
  trans |u n - l| + |v n - l'|
  apply abs_add
  linarith [fact₁, fact₂]

```lean
-- omit
  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}
```

我们来做一些类似的事情：挤压定理。

```lean
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  -- sorry
  intros ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  rcases hw ε ε_pos with ⟨N', hN'⟩
  use max N N'
  intros n hn
  rw [ge_max_iff] at hn
  specialize hN n (by linarith)
  specialize hN' n (by linarith)
  specialize h n
  specialize h' n
  rw [abs_le] at *
  constructor
  -- Here `linarith` can finish, but on paper we would write
  calc
    -ε ≤ u n - l := by linarith
     _ ≤ v n - l := by linarith
  calc
    v n - l ≤ w n - l := by linarith
          _ ≤ ε := by linarith
  -- sorry
}
```

在下一个练习中，我们将使用

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

回忆一下，我们在文件开始时列出了三种三角形不等式。

```lean
-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  -- sorry
  intros hl hl'
  apply eq_of_abs_sub_le_all
  intros ε ε_pos
  rcases hl (ε/2) (by linarith) with ⟨N, hN⟩
  rcases hl' (ε/2) (by linarith) with ⟨N', hN'⟩
  calc
    |l - l'| ≤ |l - u (max N N')| + |u (max N N') - l'| := by apply abs_sub_le
           _ = |u (max N N') - l| + |u (max N N') - l'| := by rw [abs_sub_comm]
           _ ≤ ε := by linarith [hN _ (le_max_left N N'), hN' _ (le_max_right N N')]
  -- sorry
}
```

让我们在进行定理证明前先练习解读定义。

```lean
def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  -- sorry
  intros ε ε_pos
  rcases h with ⟨inf_M, sup_M_ep⟩
  rcases sup_M_ep ε ε_pos with ⟨n₀, hn₀⟩
  use n₀
  intros n hn
  rw [abs_le]
  constructor <;> linarith [inf_M n, h' n₀ n hn]
  -- sorry
}
```

我们现在将探索子序列。

我们将要使用的新定义是，如果 `φ : ℕ → ℕ` 是（严格）递增的，那么它就是一个提取。

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

以下的 `φ` 将总是表示一个从 `ℕ` 到 `ℕ` 的函数。

下一个引理通过简单的归纳证明，但是我们在这个教程中还没有看到归纳。如果你玩过自然数游戏，那么你可以删除下面的证明并尝试重新构建它。

一个提取操作大于 id

```lean
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}
```

在这个练习中，我们使用了 `∃ n ≥ N, ...` ，这是 `∃ n, n ≥ N ∧ ...` 的缩写形式。

提取将对任意大的输入取任意大的值。

```lean
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  -- sorry
  intro h N N'
  use max N N'
  constructor
  apply le_max_right
  calc
    N ≤ max N N' := by apply le_max_left
    _ ≤ φ (max N N') := by apply id_le_extraction' h
  -- sorry
}
```

一个实数 `a` 是序列 `u` 的聚点，
如果 `u` 有一个子序列收敛于 `a`。

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`

如果 `a` 是 `u` 的聚点，那么对于任意大的输入，`u` 的值可以任意接近 `a`。

```lean
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  -- sorry
  intro hyp ε ε_pos N
  rcases hyp with ⟨φ, φ_extr, hφ⟩
  cases' hφ ε ε_pos with N' hN'
  rcases extraction_ge φ_extr N N' with ⟨q, hq, hq'⟩
  exact ⟨φ q, hq', hN' _ hq⟩
  -- sorry
}
```

如果 `u` 趋向于 `l`，那么其子序列也趋向于 `l`。

```lean
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  -- sorry
  intro ε ε_pos
  cases' h ε ε_pos with N hN
  use N
  intro n hn
  apply hN
  calc
    N ≤ n := hn
    _ ≤ φ n := id_le_extraction' hφ n
  -- sorry
}
```

如果 `u` 趋于 `l`，那么它的所有聚点都等于 `l`。

```lean
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  -- sorry
  rcases ha with ⟨φ, φ_extr, lim_u_φ⟩
  have lim_u_φ' : seq_limit (u ∘ φ) l := subseq_tendsto_of_tendsto' hl φ_extr
  exact unique_limit lim_u_φ lim_u_φ'
  -- sorry
}
```

Cauchy序列

一个序列 ` {a_n} ` 被称为 Cauchy 序列，如果对于任意一个小于 0 且大于 限制性数字epsilon存在一个带有足够大基数的 ` N ` ，使得：` ∀m,n>N, |a_m-a_n|<ε `。

为了更形象的描述 Cauchy 序列的定义，我们可以想象，随着 ` N ` 的增大，` a_n ` 序列的元素越来越接近，这些元素组成的距离会无限接近等于 0。
        
在真实数的集合中，一个序列 ` {a_n} ` 是 Cauchy 序列的充分必要条件是该序列有限。

## **定理**

在实数面板中，每一个 Cauchy 序列 ` {a_n} ` 都有极限。

**证明：**

年考虑 ` {a_n} ` 是一个 Cauchy 序列。通过序列 ` {a_n} ` 的有限性，我们可以证明 ` {a_n} ` 是一个有界序列。

• 确定 ` N1 ` 使 ` |a_m - a_n| < 1 ` 对于所有 ` m,n > N1 `。

• 选择 `N=max{N1, a_1, a_2, ..., a_N1} `。

因此，以下的不等式成立：

`-N ≤ a_n ≤ N ` 对于所有 ` n ` ，这意味着 ` {a_n} ` 是一个有界序列。

通过 Bolzano-Weierstrass 定理，每一个有界序列都有收敛的子序列。因此，我们可以找出 ` {a_n} ` 的收敛子序列 ` {a_nk} ` ，这个子序列收敛到 ` l `。

我们想要证明最初的序列 ` {a_n} ` 也收敛到 ` l `。

• 确定 ` N2 ` 使 ` |a_nk - a_nl| < ε/2 ` 对于所有 ` k,l > N2 `。

• 确定 ` N3 ` 使 ` |a_n - l| < ε/2 ` ，对于所有 ` n > N3 `。

• 选择 ` N = max{N2, N3} `。这对于所有的 ` n > N ` 和 ` m > N ` ，以下的不等式都成立：

` |a_n - a_m| ≤ |a_n - l| + |l - a_m| < ε/2 + ε/2 = ε `。

通过三角不等式，我们得出结论，` {a_n} ` 是收敛到 ` l ` 的。证明结束。

```lean
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  -- sorry
  intro hyp
  cases' hyp with l hl
  intro ε ε_pos
  cases' hl (ε / 2) (by positivity) with N hN
  use N
  intro p q hp hq
  calc
    |u p - u q| = |u p - l + (l - u q)| := by ring_nf
    _ ≤ |u p - l| + |l - u q| := by apply abs_add
    _ = |u p - l| + |u q - l| := by rw [abs_sub_comm (u q) l]
    _ ≤ ε := by linarith [hN p hp, hN q hq]
  -- sorry
}
```

在下一个练习中，你可以重复使用
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε

```lean
example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  -- sorry
  intro ε ε_pos
  cases' hu (ε / 2) (by positivity) with N hN
  use N
  have clef : ∃ N' ≥ N, |u N' - l| ≤ ε / 2
  apply near_cluster hl (ε / 2) (by positivity)
  cases' clef with N' h
  cases' h with hNN' hN'
  intro n hn
  calc
    |u n - l| = |u n - u N' + (u N' - l)| := by ring_nf
    _ ≤ |u n - u N'| + |u N' - l| := by apply abs_add
    _ ≤ ε := by linarith [hN n N' hn hNN', hN']
  -- sorry
```
