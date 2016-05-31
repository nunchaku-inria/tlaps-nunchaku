theory Untyped_Set
imports Main
begin
                                                    
section {* Untyped Set Theory as in TLA+ *}

subsection {* Basic Setup *}

definition unique_unsafe :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "unique_unsafe P = (if \<exists>x. P x then The P else Nitpick.unknown)"

typedef u = "UNIV :: ind set"
  by simp

typedecl \<alpha>

consts \<gamma> :: "\<alpha> \<Rightarrow> u"

nitpick_params [user_axioms, dont_box, max_potential = 0, show_all,
  atoms u = a b c d e f g h i j k l,
  atoms \<alpha> = \<alpha> \<beta> \<gamma> \<delta> \<epsilon> \<zeta> \<eta> \<theta> \<iota> \<kappa> \<mu> \<nu>]

definition ex\<alpha> :: "u \<Rightarrow> bool" where
  "ex\<alpha> x \<longleftrightarrow> (\<exists>a. \<gamma> a = x)"

subsection {* Set Membership *}

axiomatization mem :: "u \<Rightarrow> u \<Rightarrow> bool" (infix "#\<in>#" 50) where
  mem_ext: "\<And>A B. A = B \<or> (\<exists>x. \<not> (\<gamma> x #\<in># \<gamma> A \<longleftrightarrow> \<gamma> x #\<in># \<gamma> B))" and
  mem_acyclic: "\<And>A. \<not> tranclp (op #\<in>#) (\<gamma> A) (\<gamma> A)"

definition Mem :: "u \<Rightarrow> u \<Rightarrow> bool" (infix "\<in>#" 50) where
  "x \<in># A \<longleftrightarrow> unique_unsafe (\<lambda>P. (P \<longleftrightarrow> x #\<in># A) \<and> ex\<alpha> x \<and> ex\<alpha> A)"

nitpick_params [card = 1-8, format mem = 2, format Mem = 2]

lemma "\<not> x \<in># A"
  nitpick [expect = genuine]
  oops

lemma "x \<in># x"
  nitpick [expect = genuine]
  oops

lemma "\<not> x \<in># x"
  nitpick [expect = none]
  sorry

lemma "x \<in># y \<Longrightarrow> \<not> y \<in># x"
  nitpick [expect = none]
  sorry

lemma "x \<in># y \<Longrightarrow> y \<in># z \<Longrightarrow> \<not> z \<in># x"
  nitpick [expect = none]
  sorry


subsection {* Empty Set *}

definition emptyset :: u where
  "emptyset = unique_unsafe (\<lambda>A. (\<forall>a. \<not> \<gamma> a #\<in># A) \<and> ex\<alpha> A)"


lemma "\<forall>x. \<not> x \<in># emptyset"
  nitpick [satisfy, expect = genuine]
  nitpick [expect = none]
  sorry

lemma "(SOME x. \<not> x \<in># A) \<in># A"
  nitpick [expect = genuine]
  nitpick [satisfy, expect = none]
  oops

lemma "\<not> (SOME x. \<not> x \<in># A) \<in># A"
  nitpick [expect = none]
  sorry


subsection {* Subset *}

definition subseteq :: "u \<Rightarrow> u \<Rightarrow> bool" (infix "\<subseteq>#" 50) where
  "subseteq A B \<longleftrightarrow> (\<forall>x. x \<in># A \<longrightarrow> x \<in># B)"


subsection {* Functions *}

axiomatization
  dom :: "u \<Rightarrow> u" and
  app :: "u \<Rightarrow> u \<Rightarrow> u" (infixl "\<cdot>" 70)
where
  app_ext: "\<And>f g. dom f = dom g \<and> (\<forall>x. x \<in># dom f \<longrightarrow> f \<cdot> x = g \<cdot> x) \<longrightarrow> f = g"

abbreviation mapsto :: "u \<Rightarrow> (u \<Rightarrow> u) \<Rightarrow> u" where
  "mapsto A f \<equiv> unique_unsafe (\<lambda>g. dom g = A \<and> (\<forall>x. x \<in># A \<longrightarrow> g \<cdot> x = f x))"

lemma "f = mapsto (dom f) (op \<cdot> f)"
  nitpick [expect = none]
  sorry


subsection {* Powerset *}

definition
  Pow :: "u \<Rightarrow> u"
where
  "Pow B = unique_unsafe (\<lambda>C. \<forall>A. A \<in># C \<longleftrightarrow> A \<subseteq># B)"

lemma "A \<in># Pow B"
  nitpick [expect = genuine] (* FIXME *)
  oops

lemma "\<not> A \<in># Pow B"
  nitpick [expect = genuine]
  oops

lemma "A \<in># Pow A"
  nitpick [expect = none]
  sorry

lemma "A \<subseteq># Pow A"
  nitpick [expect = genuine]
  oops


subsection {* Big Union *}

definition
  Union :: "u \<Rightarrow> u"
where
  "Union B = unique_unsafe (\<lambda>C. \<forall>x. x \<in># C \<longleftrightarrow> (\<exists>A. x \<in># A \<and> A \<in># B))"

lemma "A \<in># Union A"
  nitpick [expect = genuine]
  oops

lemma "\<not> A \<in># Union A"
  nitpick [expect = none]
  sorry

lemma "A = Union (Pow A)"
  nitpick [expect = none]
  sorry

end
