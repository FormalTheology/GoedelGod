echo "Recomputation of the experiments from the ECAI-2014 paper *Automating Goedel\'s Ontological Proof of God\'s Existence with Higher-order Automated Theorem Provers* by Christoph Benzmueller and Bruno Woltzenlogel Paleo."
echo ""
echo "The problems tested below corresponf to the results mentioned in Figure 2 of that paper (min/max refers to the sets of dependencies tested for each conjecture statement, and the meaning of vary/const is obvious)."
echo ""
./call_tptp.sh T1_K_const_max.p T1_K_const_min.p T1_K_vary_max.p T1_K_vary_min.p T1_varying.p C_K_const_max.p  C_K_const_min.p  C_K_vary_max.p   C_K_vary_min.p T2_K_const_max.p  T2_K_const_min.p  T2_K_vary_max.p   T2_K_vary_min.p  T3_KB_const_max.p  T3_KB_const_min.p  T3_KB_vary_max.p   T3_KB_vary_min.p   T3_K_const_max.p   T3_K_const_min.p   T3_K_vary_max.p    T3_K_vary_min.p   MC_KB_const_max.p  MC_KB_const_min.p  MC_KB_vary_max.p   MC_KB_vary_min.p   FG_KB_const_max.p  FG_KB_const_min.p  FG_KB_vary_max.p   FG_KB_vary_min.p  MT_KB_const_max.p  MT_KB_const_min.p  MT_KB_vary_max.p   MT_KB_vary_min.p   CO_KB_const_max.p  CO_KB_vary_max.p  CO\'_KB_const_max.p  CO\'_KB_const_min.p  CO\'_KB_vary_max.p   CO\'_KB_vary_min.p  
echo ""
echo "Done with the experiments."
