touch ExperimentResults.txt
rm ExperimentResults.txt
touch ExperimentResults.txt
./call_tptp.sh D_EntailsInS4_A2.p >> ExperimentResults.txt			
./call_tptp.sh D_EntailsInS4_A3.p >> ExperimentResults.txt		
./call_tptp.sh D_EntailsInS4_A4.p >> ExperimentResults.txt		
./call_tptp.sh D_EntailsInS4_Def1.p >> ExperimentResults.txt		
./call_tptp.sh Def1+A2+A3+A4_Entails_D.p >> ExperimentResults.txt
./call_tptp.sh Def1+A2+A3+A4_Entails_D-Case2.p >> ExperimentResults.txt
./call_tptp.sh Def1+A2+A3+A4_Entails_D-Case1.p >> ExperimentResults.txt	
./call_tptp.sh Def1+A2+A3+A4_Entails_D-CasesCombined.p >> ExperimentResults.txt
./call_tptp.sh GodTheorem.p >> ExperimentResults.txt
./call_tptp.sh ModalCollapse.p >> ExperimentResults.txt