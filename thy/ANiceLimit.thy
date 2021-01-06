theory ANiceLimit
  imports  "HOL-Real_Asymp.Real_Asymp"
begin

(* With help from Manuel Eberl on Zulip *)

(* Reminder of different forms:

translations
  "LIM x F1. f :> F2" == "CONST filterlim (\<lambda>x. f) F2 F1"

abbreviation (in topological_space)
  tendsto :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool"  (infixr "\<longlongrightarrow>" 55)
  where "(f \<longlongrightarrow> l) F \<equiv> filterlim f (nhds l) F"

*)


lemma \<open>filterlim (\<lambda>x::real. (1 + 1 / x) powr x) (nhds (exp 1)) at_top\<close>
  by real_asymp

lemma x1:
  fixes a::real 
  assumes "a > 0" 
  shows "((\<lambda>x. a powr x) \<longlongrightarrow> 1) (at_right 0)"
(*  shows "filterlim (\<lambda>x::real. a powr x) (at_right 1) (at_right 0)"*)
using assms by real_asymp

lemma "a \<in> {0<..<1} \<Longrightarrow> filterlim (\<lambda>x::real. a powr x) (at_left 1) (at_right 0)"
      "a > 1 \<Longrightarrow> filterlim (\<lambda>x::real. a powr x) (at_right 1) (at_right 0)"
  by real_asymp+


sledgehammer_params[debug=true,timeout=600]


lemma  xx2:
  fixes a::real 
  assumes "a > 0" 
  shows "LIM (x::real) at_right 0. a powr x :> nhds 1"  using x1 assms by simp


lemma xx3:
 fixes a::real 
  assumes "a > 0" 
  shows "((\<lambda>x. a powr x) has_real_derivative ln a * a powr x) (at x)"
proof -
  have "((\<lambda>_. a) has_real_derivative 0) (at x)" by simp
  moreover have "((\<lambda>x. x) has_real_derivative 1) (at x)" by simp
  ultimately show ?thesis using   DERIV_powr[of "\<lambda>_.a" 0 x "\<lambda>x. x" 1] assms 
    by (simp add: mult.commute)
qed

lemma  xx:
  fixes a::real 
  assumes "a > 0" 
  shows "LIM x at_right 0. (a powr x - 1) / x :> nhds (ln a)"
proof -
  let ?f' = "\<lambda>x. (ln a) * (a powr x)" 
  let ?g' = "\<lambda>_. 1::real"
  show ?thesis 
proof(rule lhopital_right_0)
  show "((\<lambda>x. a powr x - 1) \<longlongrightarrow> 0) (at_right 0)" using assms by real_asymp
  show " ((\<lambda>x. x) \<longlongrightarrow> 0) (at_right 0)" using assms by simp
  show " \<forall>\<^sub>F x in at_right 0. x \<noteq> 0"  
    using eventually_at_filter not_eventuallyD by blast
  show " \<forall>\<^sub>F x::real in at_right 0. ?g' x \<noteq> (0::real)"   
    unfolding eventually_at_filter apply(eventually_elim,rule,rule)
    by simp
             
  show "\<forall>\<^sub>F x in at_right 0. ((\<lambda>x. a powr x - 1) has_real_derivative ?f' x) (at x)" 
    unfolding eventually_at_filter apply(eventually_elim,rule)
  proof 
    fix x::real
    assume "x \<noteq> 0" and "x \<in> {0<..}"
    show "((\<lambda>x. a powr x - 1) has_real_derivative ln a * a powr x) (at x) "
      using xx3 assms DERIV_minus DERIV_add sorry
  qed
  show " \<forall>\<^sub>F x in at_right 0. ((\<lambda>x. x) has_real_derivative ?g' x) (at x)"  
    by simp
  show " LIM x at_right 0. ?f' x / ?g' x :> nhds  (ln a)"  using assms by real_asymp
qed
qed

lemma yy:
  fixes a b :: real
  assumes "a > 0" "b > 0"
  shows   "((\<lambda>x. ((a powr (1/x) + b powr (1/x)) / 2) powr x) \<longlongrightarrow> exp ((ln a + ln b) / 2)) at_top"
  using assms by real_asymp


lemma bob:
  fixes f::"nat \<Rightarrow> real" and g::"real \<Rightarrow> real"
  assumes  "\<forall>n. f n = g n" and  "(g \<longlongrightarrow> c) at_top"
  shows "f \<longlonglongrightarrow> c"
  using assms tendsto_cong[of g f at_top c] 
  by (smt eventually_elim2 filterlim_iff filterlim_real_sequentially)

lemma 
  fixes a::real and b::real
  assumes "a > 0" and "b > 0"
  shows "(\<lambda>n. ( (root  n a + root n b )  / 2)^n) \<longlonglongrightarrow> (sqrt(a*b))"
proof -
  have "(\<lambda>n. ( (root  n a + root n b )  / 2)^n) = ((\<lambda>x. ((a powr (1/x) + b powr (1/x)) / 2) powr x))" sorry
  moreover have "(sqrt(a*b)) = exp ((ln a + ln b) / 2)" sorry
  ultimately show ?thesis using yy[OF assms] bob by force
qed
  





end

