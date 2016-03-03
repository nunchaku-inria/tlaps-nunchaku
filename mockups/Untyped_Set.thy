theory Untyped_Set
imports Main
begin

section {* Untyped Set Theory as in TLA+ *}

subsection {* Set Membership *}

typedecl u

text \<open>
Declare @{typ u} with an "infinite" annotation in Nunchaku, to exploit its
approximation of quantifiers and polarity analysis.
\<close>

nitpick_params [show_all, atoms u = a b c d e f g h i j k l]

axiomatization mem :: "u \<Rightarrow> u \<Rightarrow> bool" (infix "\<in>#" 50) where
  mem_ext: "\<And>A B. A = B \<or> (\<exists>x. \<not> (x \<in># A \<longleftrightarrow> x \<in># B))" and
  mem_acyclic: "\<And>A. \<not> tranclp (op \<in>#) A A"

nitpick_params [user_axioms, format mem = 2]

lemma "x \<in># A"
  nitpick [expect = genuine]
  oops

lemma "\<not> x \<in># A"
  nitpick [expect = genuine]
  oops

lemma "x \<in># x"
  nitpick [expect = genuine]
  oops

lemma "\<not> x \<in># x"
  nitpick [expect = none]
  oops

lemma "x \<in># y \<Longrightarrow> \<not> y \<in># x"
  nitpick [expect = none]
  oops

lemma "x \<in># y \<Longrightarrow> y \<in># z \<Longrightarrow> \<not> z \<in># x"
  nitpick [expect = none]
  oops


subsection {* Functions *}

axiomatization
  dom :: "u \<Rightarrow> u" and
  app :: "u \<Rightarrow> u \<Rightarrow> u" (infixl "\<cdot>" 70)
where
  app_ext: "\<And>A B. dom A = dom B \<and> (\<forall>x. x \<in># dom A \<longrightarrow> f \<cdot> x = g \<cdot> x) \<longrightarrow> f = g"

end
