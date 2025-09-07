```lean
import Mathlib.Probability.Notation
import GlimpseOfLean.Library.Probability
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
noncomputable section
open scoped ENNReal
```


# 概率测度，独立集合

我们引入一个概率空间和该空间上的事件（可测集合）。然后我们定义事件的独立性和条件概率，并证明与这两个概念相关的结果。

Mathlib 有一个（不同的）集合独立性定义，也有给定集合的条件测度。在这里，我们改为练习简单的新定义，以应用前面文件中介绍的策略。

我们打开命名空间。这样做的效果是，在该命令之后，我们可以调用这些命名空间中的引理而不需要它们的命名空间前缀：例如，我们可以写 `inter_comm` 而不是 `Set.inter_comm`。将鼠标悬停在 `open` 上以了解更多信息。

```lean
open MeasureTheory ProbabilityTheory Set

```

我们定义一个测度空间 `Ω`：`MeasureSpace Ω` 变量声明 `Ω` 是一个可测空间，其上有一个规范测度 `volume`，记号为 `ℙ`。然后我们声明 `ℙ` 是一个概率测度。也就是说，`ℙ univ = 1`，其中 `univ : Set Ω` 是 `Ω` 中的全集（包含所有 `x : Ω` 的集合）。

```lean
variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

-- `A, B` 将表示 `Ω` 中的集合。
variable {A B : Set Ω}

```

我们可以取集合 `A` 的测度：`ℙ A : ℝ≥0∞`。`ℝ≥0∞`，或者 `ENNReal`，是扩展非负实数的类型，它包含 `∞`。测度通常可以取无穷值，但由于我们的 `ℙ` 是概率测度，它实际上只取到 1 的值。`simp` 知道概率测度是有限的，会使用引理 `measure_ne_top` 或 `measure_lt_top` 来证明 `ℙ A ≠ ∞` 或 `ℙ A < ∞`。

提示：使用 `#check measure_ne_top` 查看该引理的作用。

`ENNReal` 上的运算不如 `ℝ` 上的运算表现良好：`ENNReal` 不是环，例如减法会截断到零。如果你发现用来转换方程的引理 `lemma_name` 不适用于 `ENNReal`，尝试找到一个名为 `ENNReal.lemma_name_of_something` 之类的引理并使用它。

- 如果 `ℙ (A ∩ B) = ℙ A * ℙ B`，则对于环境概率测度 `ℙ`，两个集合 `A, B` 是独立的。

```lean
def IndepSet (A B : Set Ω) : Prop := ℙ (A ∩ B) = ℙ A * ℙ B

```

- 如果 `A` 独立于 `B`，则 `B` 独立于 `A`。

```lean
lemma IndepSet.symm : IndepSet A B → IndepSet B A := by
  -- sorry
  intro h
  unfold IndepSet
  unfold IndepSet at h
  rw [inter_comm, mul_comm]
  exact h
  -- sorry

```

测度论中的许多引理需要集合是可测的（`MeasurableSet A`）。如果你遇到形如 `⊢ MeasurableSet (A ∩ B)` 的目标，尝试 `measurability` 策略。该策略产生可测性证明。

```lean
-- 提示：`compl_eq_univ_diff`，`measure_diff`，`inter_univ`，`measure_compl`，`ENNReal.mul_sub`
lemma IndepSet.compl_right (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A B → IndepSet A Bᶜ := by
  -- sorry
  intro h
  unfold IndepSet
  unfold IndepSet at h
  rw [measure_compl hB (measure_ne_top _ _)]
  rw [measure_univ]
  rw [compl_eq_univ_diff]
  rw [inter_diff_distrib_left]
  rw [inter_univ]
  rw [measure_diff]
  · rw [ENNReal.mul_sub]
    rw [mul_one]
    rw [h]
    simp
  · simp
  · measurability
  · simp
  -- sorry

```

应用 `IndepSet.compl_right` 来证明这个泛化。为一些常用引理添加 iff 版本是良好的做法，这使我们能在 `rw` 策略中使用它们。

```lean
lemma IndepSet.compl_right_iff (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IndepSet A Bᶜ ↔ IndepSet A B := by
  -- sorry
  constructor
  · intro h
    rw [← compl_compl B]
    apply IndepSet.compl_right hA hB.compl
    exact h
  · intro h
    exact compl_right hA hB h
  -- sorry

-- 使用到目前为止你已经证明的内容
lemma IndepSet.compl_left (hA : MeasurableSet A) (hB : MeasurableSet B) (h : IndepSet A B) :
    IndepSet Aᶜ B := by
  -- sorry
  apply IndepSet.symm
  apply IndepSet.compl_right hB hA
  apply IndepSet.symm
  exact h
  -- sorry

```

你能按照上面的例子写出并证明一个引理 `IndepSet.compl_left_iff` 吗？

```lean
-- 你的引理在这里

-- 提示：`ENNReal.mul_self_eq_self_iff`
lemma indep_self (h : IndepSet A A) : ℙ A = 0 ∨ ℙ A = 1 := by
  -- sorry
  unfold IndepSet at h
  rw [inter_self] at h
  symm at h -- TODO 也许它还没有被介绍
  rw [ENNReal.mul_self_eq_self_iff] at h
  simp at h
  exact h
  -- sorry

```


### 条件概率


- 集合 `A` 在 `B` 条件下的概率。

```lean
def condProb (A B : Set Ω) : ENNReal := ℙ (A ∩ B) / ℙ B

```

我们为 `condProb A B` 定义一个记号，使其看起来更像纸面数学。

```lean
notation3 "ℙ("A"|"B")" => condProb A B

```

现在我们已经定义了 `condProb`，我们想使用它，但 Lean 对它一无所知。我们可以每个证明都从 `rw [condProb]` 开始，但更方便的做法是首先写出关于 `condProb` 性质的引理，然后使用那些引理。

```lean
-- 提示：`measure_inter_null_of_null_left`
@[simp] -- 这使得引理可以被 `simp` 使用
lemma condProb_zero_left (A B : Set Ω) (hA : ℙ A = 0) : ℙ(A|B) = 0 := by
  -- sorry
  unfold condProb
  simp [measure_inter_null_of_null_left _ hA]
  -- sorry

@[simp]
lemma condProb_zero_right (A B : Set Ω) (hB : ℙ B = 0) : ℙ(A|B) = 0 := by
  -- sorry
  unfold condProb
  simp [measure_inter_null_of_null_right _ hB]
  -- sorry

```

还有哪些其他基本引理可能有用？是否还有其他"特殊"集合，对于它们 `condProb` 取已知值？

```lean
-- 你的引理在这里

```

下面的陈述是一个 `theorem` 而不是 `lemma`，因为我们认为它很重要。这两个关键字之间没有功能差异。

- **贝叶斯定理**

```lean
theorem bayesTheorem (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by
  by_cases h : ℙ A = 0 -- 这个策略执行情况分析。
  -- 观察创建的目标，特别是两个目标中的 `h` 假设
```

```lean
  ·
```

inline sorry

```lean
simp [h] /- inline sorry -/
  -- sorry
  unfold condProb
  rw [ENNReal.mul_div_cancel h]
  · rw [inter_comm]
  · simp
  -- sorry

```

你真的需要所有这些假设吗？在 Lean 中，除以零遵循惯例 `a/0 = 0` 对所有 a 成立。这意味着我们可以证明贝叶斯定理而不需要 `ℙ A ≠ 0` 和 `ℙ B ≠ 0`。然而，这是形式化的怪癖，而不是标准的数学陈述。如果你想了解更多关于除法在 Lean 中如何工作的信息，尝试用鼠标悬停在 `/` 上。

```lean
theorem bayesTheorem' (A B : Set Ω) : ℙ(A|B) = ℙ A * ℙ(B|A) / ℙ B := by
  -- sorry
  by_cases h : ℙ A = 0
  · simp [h]
  unfold condProb
  rw [ENNReal.mul_div_cancel h]
  · rw [inter_comm]
  · simp
  -- sorry

lemma condProb_of_indepSet (h : IndepSet B A) (hB : ℙ B ≠ 0) : ℙ(A|B) = ℙ A := by
  -- sorry
  unfold condProb
  rw [h.symm, mul_div_assoc, ENNReal.div_self, mul_one]
  · exact hB
  · simp
  -- sorry

```