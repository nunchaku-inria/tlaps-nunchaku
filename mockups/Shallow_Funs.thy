theory Shallow_Funs
imports Main
begin


section {* Examples *}

datatype int = Zero | One | Two

lemma
  fixes
    f :: "int \<rightharpoonup> int"
  assumes
    f_dom: "\<forall>x. f x = None \<longleftrightarrow> x \<noteq> Zero" and
    f_ran: "\<forall>x. f x = None \<or> f x = Some Zero"
  shows
    "the (f Zero) = Zero"
  nitpick [satisfy, expect = genuine]
  oops

lemma
  fixes
    f :: "int \<rightharpoonup> int" and
    g :: "int \<rightharpoonup> int"
  assumes
    f_dom: "dom f = {Zero}" and
    f_ran: "ran f = {Zero}" and
    g_dom: "dom g = {Zero}" and
    g_ran: "ran g = {Zero}"
  shows
    "f = g"
  nitpick [expect = none]
  oops

lemma
  fixes
    f :: "int \<rightharpoonup> int" and
    g :: "int \<rightharpoonup> int"
  assumes
    f_dom: "\<forall>x. f x = None \<longleftrightarrow> x \<noteq> Zero" and
    f_ran: "\<forall>x. f x = None \<or> f x = Some Zero" and
    g_dom: "\<forall>x. g x = None \<longrightarrow> x \<noteq> Zero" and
    g_ran: "\<forall>x. g x = None \<or> g x = Some Zero"
  shows
    "\<forall>x. f x = g x"
  nitpick [expect = genuine]
  oops

end
