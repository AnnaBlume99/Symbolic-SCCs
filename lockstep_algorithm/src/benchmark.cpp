#include <filesystem>
#include <list>
#include <string>
#include <deque>
#include <iostream>
#include <deque>
#include <algorithm>
#include <chrono>
#include <vector>
#include <fstream>
#include <math.h>

#include <sylvan.h>
#include <sylvan_table.h>
#include <sylvan_obj.hpp>

#include "benchmark.h"
#include "scc.h"
#include "petriTranslation.h"
#include "bdd_utilities.h"
#include "graph_creation.h"
#include "print.h"
#include "../test/graph_examples.h"
#include "bscc.h"
#include "parse.h"

std::list<std::string> getPintStrings() {
  std::list<std::string> resultList = {};

  resultList.push_back("../PintFiles/model.an");
  //resultList.push_back("../PintFiles/apoptosis_network.an");
  resultList.push_back("../PintFiles/apoptosis_stable.an");
  //resultList.push_back("../PintFiles/cell_collective_vut.an");
  resultList.push_back("../PintFiles/g2a.an");
  resultList.push_back("../PintFiles/g2a_with_names.an");
  //resultList.push_back("../PintFiles/hmox1_pathway.an");
  //resultList.push_back("../PintFiles/[v101]__[r158]__[T-CELL-RECEPTOR-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v102]__[r157]__[INTERFERON-1]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v104]__[r166]__[ETC]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v104]__[r226]__[EGFR-ERBB-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v10]__[r14]__[AP-1-ELSE-0-WT]__[ginsim].an");
  resultList.push_back("../PintFiles/[v10]__[r18]__[ROOT-STEM-CELL-NICHE]__[biomodels].an");
  resultList.push_back("../PintFiles/[v10]__[r27]__[FISSION-YEAST-DAVIDICH-2008]__[ginsim].an");
  resultList.push_back("../PintFiles/[v10]__[r34]__[BOOLEAN-CELL-CYCLE]__[ginsim].an");
  resultList.push_back("../PintFiles/[v10]__[r35]__[MAMMALIAN-CELL-CYCLE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v110]__[r212]__[RODRIGUEZ-JORGE-TCR-SIGNALLING-17-07-2018]__[ginsim].an");
  resultList.push_back("../PintFiles/[v118]__[r218]__[IL1-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v11]__[r11]__[TOLL-PATHWAY-12-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v11]__[r11]__[TOLL-PATHWAY-OF-DROSOPHILA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v120]__[r195]__[COAGULATION-PATHWAY]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v12]__[r30]__[METABOLIC-INTERACTIONS-IN-THE-GUT-MICROBIOME]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v131]__[r302]__[INFLUENZA-VIRUS-REPLICATION-CYCLE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v139]__[r557]__[SIGNAL-TRANSDUCTION-IN-FIBROBLASTS]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v13]__[r18]__[REGULATION-OF-THE-LARABINOSE-OPERON]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v13]__[r22]__[LAC-OPERON]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v14]__[r66]__[ARABIDOPSIS-THALIANA-CELL-CYCLE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v15]__[r38]__[CARDIAC-DEVELOPMENT]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v15]__[r38]__[PREDICTING-VARIABLES-IN-CARDIAC-GENE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v15]__[r66]__[FANCONI-ANEMIA-AND-CHECKPOINT-RECOVERY]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v165]__[r275]__[VIRUS-REPLICATION-CYCLE]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v168]__[r243]__[HMOX1-PATHWAY]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v16]__[r22]__[NEUROTRANSMITTER-SIGNALING-PATHWAY]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v16]__[r41]__[SKBR3-BREAST-CELL-LINE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v16]__[r46]__[BT474-BREAST-CELL-LINE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v16]__[r46]__[HCC1954-BREAST-CELL-LINE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v16]__[r58]__[MAPK-RED3-19-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v17]__[r29]__[DROSOPHILA-BODY-SEGMENTATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v17]__[r78]__[MAPK-RED1-19-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v188]__[r351]__[CD4-T-CELL-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v18]__[r18]__[VEGF-PATHWAY-12-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v18]__[r18]__[VEGF-PATHWAY-OF-DROSOPHILA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v18]__[r43]__[TLGL-SURVIVAL-NETWORK]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v18]__[r58]__[BUDDING-YEAST-IRONS-2009]__[ginsim].an");
  resultList.push_back("../PintFiles/[v18]__[r59]__[BUDDING-YEAST-CELL-CYCLE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v18]__[r60]__[MAPK-RED2-12-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v18]__[r78]__[CD4-T-CELL-DIFFERENTIATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v18]__[r83]__[T-CD4-LYMPHOCYTE-TRANSCRIPTION]__[biomodels].an");
  resultList.push_back("../PintFiles/[v193]__[r328]__[KYNURENINE-PATHWAY]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v19]__[r21]__[JNK-PATHWAY]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v19]__[r32]__[OXIDATIVE-STRESS-PATHWAY]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v19]__[r73]__[INFLAMMATORY-RESPONSES]__[biomodels].an");
  resultList.push_back("../PintFiles/[v19]__[r79]__[HUMAN-GONADAL-SEX-DETERMINATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v205]__[r269]__[ER-STRESS]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v20]__[r48]__[ERB-B2]__[ginsim].an");
  resultList.push_back("../PintFiles/[v20]__[r51]__[MAMMALIAN-CELL-CYCLE-1607]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v20]__[r88]__[SUPP-MAT-MOD-NET]__[ginsim].an");
  resultList.push_back("../PintFiles/[v21]__[r24]__[TGFB-pathway]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v22]__[r39]__[B-CELL-DIFFERENTIATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v23]__[r24]__[FGF-PATHWAY-12-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v23]__[r24]__[FGF-PATHWAY-OF-DROSOPHILA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v23]__[r34]__[T-CELL-DIFFERENTIATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v23]__[r43]__[AURORA-KINASE-A-IN-NEUROBLASTOMA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v247]__[r1100]__[ERBB-14-RECEPTOR-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v24]__[r28]__[PROCESSING-OF-SPZ-NETWORK-FROM-DROSOPHILA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v24]__[r28]__[SPZ-PROCESSING-12-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v24]__[r32]__[HH-PATHWAY-11-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v24]__[r32]__[HH-PATHWAY-OF-DROSOPHILA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v24]__[r48]__[TOL-REGULATORY-NETWORK]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v25]__[r67]__[S-PHASE-ENTRY-SIGNALLING-PATHWAY]__[biomodels].an");
  resultList.push_back("../PintFiles/[v25]__[r70]__[BT474-BREAST-CELL-LINE-LONGTERM]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v25]__[r70]__[HCC1954-BREAST-CELL-LINE-LONGTERM]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v25]__[r81]__[SKBR3-BREAST-CELL-LINE-LONGTERM]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v260]__[r258]__[NSP9-PROTEIN]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v26]__[r28]__[WG-PATHWAY-11-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v26]__[r29]__[WG-PATHWAY-OF-DROSOPHILA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v26]__[r58]__[TRICHOSTRONGYLUS-RETORTAEFORMIS]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v26]__[r79]__[HSPC-MSC-0]__[ginsim].an");
  resultList.push_back("../PintFiles/[v26]__[r81]__[PROINFLAMMATORY-TUMOR-MICROENVIRONMENT]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v28]__[r123]__[FA-BRCA-PATHWAY]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v28]__[r45]__[CALZONE-CELL-FATE]__[ginsim].an");
  resultList.push_back("../PintFiles/[v28]__[r45]__[DEATH-RECEPTOR-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v29]__[r128]__[BLOOD-STEM-CELL-NETWORK]__[biomodels].an");
  resultList.push_back("../PintFiles/[v31]__[r36]__[APOPTOSIS]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v31]__[r50]__[SEPARATION-INITIATION-NETWORK]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v321]__[r533]__[SIGNALING-IN-MACROPHAGE-ACTIVATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v32]__[r156]__[TUMOR-CELL-INVASION-AND-MIGRATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v33]__[r52]__[CELL-FATE-MULTISCALE]__[ginsim].an");
  resultList.push_back("../PintFiles/[v33]__[r79]__[BORDETELLA-BRONCHISEPTICA]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v33]__[r94]__[LYMPHOID-AND-MYELOID-CELL-SPECIFICATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v34]__[r40]__[RTC-AND-TRANSCRIPTION]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v34]__[r43]__[CHOLESTEROL-REGULATORY-PATHWAY]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v351]__[r737]__[NSP14]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v38]__[r38]__[E-PROTEIN]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v38]__[r96]__[CD4-T-CELL-DIFFERENTIATION-6678]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v40]__[r53]__[T-CELL-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v40]__[r57]__[TCR-SIG-40]__[ginsim].an");
  resultList.push_back("../PintFiles/[v41]__[r73]__[APOPTOSIS-NETWORK]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v42]__[r51]__[TREATMENT-OF-PROSTATE-CANCER]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v44]__[r78]__[GUARD-CELL-ABSCISIC-ACID-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v47]__[r49]__[ORF3A]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v48]__[r52]__[IFN-LAMBDA]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v49]__[r167]__[STOMATAL-OPENING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v50]__[r97]__[DIFFERENTIATION-OF-T-LYMPHOCYTES]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v51]__[r96]__[SENESCENCE-ASSOCIATED-SECRETORY-PHENOTYPE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v52]__[r92]__[ORF10-CUL2-PATHWAY]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v53]__[r104]__[MAPK-CANCER-CELL-FATE]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v53]__[r104]__[MAPK-LARGE-19-06-2013]__[ginsim].an");
  resultList.push_back("../PintFiles/[v53]__[r135]__[B-BRONCHISEPTICA-AND-T-RETORTAEFORMIS]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v5]__[r14]__[CORTICAL-AREA-DEVELOPMENT]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v5]__[r15]__[G2A]__[ginsim].an");
  resultList.push_back("../PintFiles/[v60]__[r193]__[T-LGL]__[ginsim].an");
  resultList.push_back("../PintFiles/[v60]__[r195]__[TLGL-SURVIVAL-NETWORK-2011]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v60]__[r62]__[NSP4-NSP6]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v61]__[r193]__[TLGL-SURVIVAL-NETWORK-2008]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v62]__[r108]__[PC12-CELL-DIFFERENTIATION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v66]__[r128]__[IMMUNE-CHECKPOINT-NETWORK]__[DOI-10.3390-cancers12123600].an");
  resultList.push_back("../PintFiles/[v66]__[r139]__[SIGNALING-PATHWAY-FOR-BUTHANOL-PRODUCTION]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v67]__[r131]__[BORTEZOMIB-RESPONSES-IN-U266]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v68]__[r103]__[HGF-SIGNALING-IN-KERATINOCYTES]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v6]__[r11]__[ZEBRA-MIR9-22-07-2011]__[ginsim].an");
  resultList.push_back("../PintFiles/[v70]__[r153]__[COLITISASSOCIATE-COLON-CANCER]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v73]__[r114]__[YEAST-APOPTOSIS]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v73]__[r97]__[GLUCOSE-REPRESSION-SIGNALING-2009]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v81]__[r160]__[LIMPHOPOIESIS-REGULATORY-NETWORK]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v85]__[r130]__[RENIN-ANGIOTENSIN]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v86]__[r149]__[IL6-SIGNALING]__[cellcollective].an");
  resultList.push_back("../PintFiles/[v91]__[r104]__[PAMP-SIGNALING]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v94]__[r132]__[PYRIMIDINE-DEPRIVATION]__[covid-uni-lu].an");
  resultList.push_back("../PintFiles/[v9]__[r12]__[G2B]__[ginsim].an");
  resultList.push_back("../PintFiles/[v9]__[r19]__[BUDDING-YEAST-ORLANDO-2008]__[ginsim].an");
  resultList.push_back("../PintFiles/[v9]__[r19]__[CELL-CYCLE-TRANSCRIPTION]__[cellcollective].an");


  return resultList;
}

std::list<std::string> getPathStringsBscc() {
  std::list<std::string> resultList = {};

  // < 15 minutes
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_a_17place.pnml");        //1 BSCCs / 16 SCCs
  resultList.push_back("GPUForwardProgress/PT/gpufp_04_a_24place.pnml");      //16 BSCCs / 368 SCCs
  resultList.push_back("ShieldRVs/PT/shield_s_rv_002_a_31place.pnml");        //8 BSCCs / 2362 SCCs
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_a_34place.pnml");      //3 BSCCs / 406 SCCs
  resultList.push_back("SmartHome/PT/smhome_01_38place.pnml");                //1 BSCCs / 76 SCCs
  resultList.push_back("GPUForwardProgress/PT/gpufp_08_a_40place.pnml");      //256 BSCCs / 118208 SCCs
  resultList.push_back("SmartHome/PT/smhome_02_41place.pnml");                //1 BSCCs / 76 SCCs
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_b_43place.pnml");        //1 BSCCs / 479 SCCs
  resultList.push_back("SmartHome/PT/smhome_03_45place.pnml");                //1 BSCCs / 76 SCCs
  resultList.push_back("ShieldRVs/PT/shield_s_rv_003_a_45place.pnml");        //51 BSCCs / 327762 SCCs
  resultList.push_back("ShieldRVt/PT/shield_t_rv_001_b_53place.pnml");        //1 BSCCs / 2909 SCCs
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_b_71place.pnml");      //3 BSCCs / 123725 SCCs
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_001_b_73place.pnml");      //1 BSCCs / 170860 SCCs
  resultList.push_back("SmartHome/PT/smhome_04_139place.pnml");               //8 BSCCs / 10126 SCCs


  // // Feasible bsccs of the larger ones *These are also in the list below*
  // resultList.push_back("GPUForwardProgress/PT/gpufp_12_a_56place.pnml");                      //56 - 90s // 4096 BSCCs
  
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_004_a_59place.pnml");                        //59 - 4 min // ??
  // resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_b_81place.pnml");                      //81 - 30s // 3 BSCCs
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_002_b_83place.pnml");                        //83 - 30s // 8 BSCCs
  // resultList.push_back("ShieldRVt/PT/shield_t_rv_002_b_103place.pnml");                       //103 - 100s //146 BSCCs
  // resultList.push_back("GPUForwardProgress/PT/gpufp_04_b_112place.pnml");                     //112 - 15s //??
  // resultList.push_back("HealthRecord/PT/hrec_01_117place.pnml");                              //117 - 8s //15 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_02_119place.pnml");                              //119 - 15s //27 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_03_121place.pnml");                              //121 - 25s //51 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_04_123place.pnml");                              //123 - 30s //99 BSCCs
  // resultList.push_back("HealthRecord/PT/hrec_05_125place.pnml");                              //125 - 40s //195 BSCCs
  // resultList.push_back("DiscoveryGPU/PT/discovery_13_a_133place.pnml");                       //133 - 2s //1 BSCCs


  // > 15 minutes - not checked yet for only 1 SCC
  //resultList.push_back("GPUForwardProgress/PT/gpufp_12_a_56place.pnml");                      //56 - 90s
  //resultList.push_back("ShieldRVs/PT/shield_s_rv_004_a_59place.pnml");                        //59 - 4 min
  //resultList.push_back("DiscoveryGPU/PT/discovery_06_a_63place.pnml");                        //63 - 1 SCC
  //resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_a_65place.pnml");                      //65 - slow
  //resultList.push_back("GPUForwardProgress/PT/gpufp_16_a_72place.pnml");                      //72 - slow
  //resultList.push_back("DiscoveryGPU/PT/discovery_07_a_73place.pnml");                        //73 - 1 SCC
  //resultList.push_back("ShieldRVs/PT/shield_s_rv_005_a_73place.pnml");                        //73 - slow
  //resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_b_81place.pnml");                      //81 - 30s
  //resultList.push_back("ShieldRVs/PT/shield_s_rv_002_b_83place.pnml");                        //83 - 30s
  //resultList.push_back("DiscoveryGPU/PT/discovery_08_a_83place.pnml");                        //83 - 1 SCC
  //resultList.push_back("GPUForwardProgress/PT/gpufp_20_a_88place.pnml");                      //88 - slow
  //resultList.push_back("DiscoveryGPU/PT/discovery_09_a_93place.pnml");                        //93 - 1 SCC
  //resultList.push_back("ShieldPPPs/PT/shield_s_ppp_003_a_96place.pnml");                      //96 - slow
  //resultList.push_back("ShieldRVt/PT/shield_t_rv_002_b_103place.pnml");                       //103 - 100s
  //resultList.push_back("DiscoveryGPU/PT/discovery_10_a_103place.pnml");                       //103 - 1 SCC
  // resultList.push_back("GPUForwardProgress/PT/gpufp_24_a_104place.pnml");                     //104 - slow
  // resultList.push_back("GPUForwardProgress/PT/gpufp_04_b_112place.pnml");                     //112 - 15s
  // resultList.push_back("DiscoveryGPU/PT/discovery_11_a_113place.pnml");                       //113 - 1 SCC
  // resultList.push_back("HealthRecord/PT/hrec_01_117place.pnml");                              //117 - 8s
  // resultList.push_back("HealthRecord/PT/hrec_02_119place.pnml");                              //119 - 15s
  // resultList.push_back("GPUForwardProgress/PT/gpufp_28_a_120place.pnml");                     //120 - slow
  // resultList.push_back("HealthRecord/PT/hrec_03_121place.pnml");                              //121 - 25s
  // resultList.push_back("HealthRecord/PT/hrec_04_123place.pnml");                              //123 - 30s
  // resultList.push_back("DiscoveryGPU/PT/discovery_12_a_123place.pnml");                       //123 - 1 SCC
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_003_b_123place.pnml");                       //123 - slow
  // resultList.push_back("HealthRecord/PT/hrec_05_125place.pnml");                              //125 - 40s
  // resultList.push_back("DiscoveryGPU/PT/discovery_13_a_133place.pnml");                       //133 - 2s
  // resultList.push_back("GPUForwardProgress/PT/gpufp_32_a_136place.pnml");                     //136 - slow
  // resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_b_139place.pnml");                     //139 - slow*/
  // resultList.push_back("DiscoveryGPU/PT/discovery_14_a_143place.pnml");                       //143
  // resultList.push_back("ShieldIIPt/PT/shield_t_iip_002_b_143place.pnml");                     //143
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_010_a_143place.pnml");                       //143
  // resultList.push_back("ShieldPPPs/PT/shield_s_ppp_004_a_127place.pnml");                     //127
  // resultList.push_back("GPUForwardProgress/PT/gpufp_36_a_152place.pnml");                     //152
  // resultList.push_back("ShieldRVt/PT/shield_t_rv_003_b_153place.pnml");                       //153
  // resultList.push_back("DiscoveryGPU/PT/discovery_15_a_153place.pnml");                       //153
  // resultList.push_back("HealthRecord/PT/hrec_06_154place.pnml");                              //154
  // resultList.push_back("HealthRecord/PT/hrec_07_155place.pnml");                              //155
  // resultList.push_back("HealthRecord/PT/hrec_08_156place.pnml");                              //156
  // resultList.push_back("HealthRecord/PT/hrec_09_157place.pnml");                              //157
  // resultList.push_back("HealthRecord/PT/hrec_10_158place.pnml");                              //158
  // resultList.push_back("ShieldPPPs/PT/shield_s_ppp_005_a_158place.pnml");                     //158
  // resultList.push_back("ShieldPPPt/PT/shield_t_ppp_002_b_159place.pnml");                     //159
  // resultList.push_back("HealthRecord/PT/hrec_11_159place.pnml");                              //159
  // resultList.push_back("HealthRecord/PT/hrec_12_160place.pnml");                              //160
  // resultList.push_back("HealthRecord/PT/hrec_13_161place.pnml");                              //161
  // resultList.push_back("HealthRecord/PT/hrec_14_162place.pnml");                              //162
  // resultList.push_back("HealthRecord/PT/hrec_15_163place.pnml");                              //163
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_004_b_163place.pnml");                       //163
  // resultList.push_back("GPUForwardProgress/PT/gpufp_40_a_168place.pnml");                     //168
  // resultList.push_back("DiscoveryGPU/PT/discovery_06_b_184place.pnml");                       //184
  // resultList.push_back("GPUForwardProgress/PT/gpufp_08_b_188place.pnml");                     //188
  // resultList.push_back("ShieldRVt/PT/shield_t_rv_004_b_203place.pnml");                       //203
  // resultList.push_back("ShieldRVs/PT/shield_s_rv_005_b_203place.pnml");                       //203
  // resultList.push_back("DiscoveryGPU/PT/discovery_07_b_212place.pnml");                       //212
  // resultList.push_back("ShieldIIPt/PT/shield_t_iip_003_b_213place.pnml");                     //213

  return resultList;
}

//These pathstrings were sorted with HumanSort *TM*
std::list<std::string> getPathStringsAll() {
  std::list<std::string> resultList = {};

  // < 15 minutes
  resultList.push_back("ShieldRVt/PT/shield_t_rv_001_a_11place.pnml");                        //11
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_a_17place.pnml");                        //17
  resultList.push_back("ShieldRVt/PT/shield_t_rv_002_a_19place.pnml");                        //19
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_001_a_22place.pnml");                      //22
  resultList.push_back("GPUForwardProgress/PT/gpufp_04_a_24place.pnml");                      //24
  resultList.push_back("ShieldRVt/PT/shield_t_rv_003_a_27place.pnml");                        //27
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_a_28place.pnml");                      //28
  resultList.push_back("ShieldRVs/PT/shield_s_rv_002_a_31place.pnml");                        //31
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_a_34place.pnml");                      //34
  resultList.push_back("ShieldRVt/PT/shield_t_rv_004_a_35place.pnml");                        //35
  resultList.push_back("SmartHome/PT/smhome_01_38place.pnml");                                //38
  resultList.push_back("GPUForwardProgress/PT/gpufp_08_a_40place.pnml");                      //40
  resultList.push_back("SmartHome/PT/smhome_02_41place.pnml");                                //41
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_002_a_41place.pnml");                      //41
  resultList.push_back("ShieldRVs/PT/shield_s_rv_001_b_43place.pnml");                        //43
  resultList.push_back("ShieldRVt/PT/shield_t_rv_005_a_43place.pnml");                        //43
  resultList.push_back("SmartHome/PT/smhome_03_45place.pnml");                                //45
  resultList.push_back("ShieldRVs/PT/shield_s_rv_003_a_45place.pnml");                        //45
  resultList.push_back("ShieldRVt/PT/shield_t_rv_001_b_53place.pnml");                        //53
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_002_a_53place.pnml");                      //53
  /*resultList.push_back("ShieldIIPt/PT/shield_t_iip_003_a_60place.pnml");                      //60
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_001_b_71place.pnml");                      //71
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_001_b_73place.pnml");                      //73
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_003_a_78place.pnml");                      //78
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_004_a_79place.pnml");                      //79
  resultList.push_back("ShieldRVt/PT/shield_t_rv_010_a_83place.pnml");                        //83
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_005_a_98place.pnml");                      //98
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_004_a_103place.pnml");                     //103
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_005_a_128place.pnml");                     //128
  resultList.push_back("SmartHome/PT/smhome_04_139place.pnml");                               //139
  resultList.push_back("ShieldRVt/PT/shield_t_rv_020_a_163place.pnml");                       //163
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_010_a_193place.pnml");                     //193
*/
  return resultList;
}

std::list<std::string> getPathStringsSlow() {
  std::list<std::string> resultList = {};

  // > 15 minutes
  resultList.push_back("GPUForwardProgress/PT/gpufp_12_a_56place.pnml");                      //56
  resultList.push_back("ShieldRVs/PT/shield_s_rv_004_a_59place.pnml");                        //59
  resultList.push_back("DiscoveryGPU/PT/discovery_06_a_63place.pnml");                        //63
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_a_65place.pnml");                      //65
  resultList.push_back("GPUForwardProgress/PT/gpufp_16_a_72place.pnml");                      //72
  resultList.push_back("DiscoveryGPU/PT/discovery_07_a_73place.pnml");                        //73
  resultList.push_back("ShieldRVs/PT/shield_s_rv_005_a_73place.pnml");                        //73
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_001_b_81place.pnml");                      //81
  resultList.push_back("ShieldRVs/PT/shield_s_rv_002_b_83place.pnml");                        //83
  resultList.push_back("DiscoveryGPU/PT/discovery_08_a_83place.pnml");                        //83
  resultList.push_back("GPUForwardProgress/PT/gpufp_20_a_88place.pnml");                      //88
  resultList.push_back("DiscoveryGPU/PT/discovery_09_a_93place.pnml");                        //93
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_003_a_96place.pnml");                      //96
  resultList.push_back("ShieldRVt/PT/shield_t_rv_002_b_103place.pnml");                       //103
  resultList.push_back("DiscoveryGPU/PT/discovery_10_a_103place.pnml");                       //103
  resultList.push_back("GPUForwardProgress/PT/gpufp_24_a_104place.pnml");                     //104
  resultList.push_back("GPUForwardProgress/PT/gpufp_04_b_112place.pnml");                     //112
  resultList.push_back("DiscoveryGPU/PT/discovery_11_a_113place.pnml");                       //113
  resultList.push_back("HealthRecord/PT/hrec_01_117place.pnml");                              //117
  resultList.push_back("HealthRecord/PT/hrec_02_119place.pnml");                              //119
  resultList.push_back("GPUForwardProgress/PT/gpufp_28_a_120place.pnml");                     //120
  resultList.push_back("HealthRecord/PT/hrec_03_121place.pnml");                              //121
  resultList.push_back("HealthRecord/PT/hrec_04_123place.pnml");                              //123
  resultList.push_back("DiscoveryGPU/PT/discovery_12_a_123place.pnml");                       //123
  resultList.push_back("ShieldRVs/PT/shield_s_rv_003_b_123place.pnml");                       //123
  resultList.push_back("HealthRecord/PT/hrec_05_125place.pnml");                              //125
  resultList.push_back("DiscoveryGPU/PT/discovery_13_a_133place.pnml");                       //133
  resultList.push_back("GPUForwardProgress/PT/gpufp_32_a_136place.pnml");                     //136
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_002_b_139place.pnml");                     //139
  resultList.push_back("DiscoveryGPU/PT/discovery_14_a_143place.pnml");                       //143
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_002_b_143place.pnml");                     //143
  resultList.push_back("ShieldRVs/PT/shield_s_rv_010_a_143place.pnml");                       //143
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_004_a_127place.pnml");                     //127
  resultList.push_back("GPUForwardProgress/PT/gpufp_36_a_152place.pnml");                     //152
  resultList.push_back("ShieldRVt/PT/shield_t_rv_003_b_153place.pnml");                       //153
  resultList.push_back("DiscoveryGPU/PT/discovery_15_a_153place.pnml");                       //153
  resultList.push_back("HealthRecord/PT/hrec_06_154place.pnml");                              //154
  resultList.push_back("HealthRecord/PT/hrec_07_155place.pnml");                              //155
  resultList.push_back("HealthRecord/PT/hrec_08_156place.pnml");                              //156
  resultList.push_back("HealthRecord/PT/hrec_09_157place.pnml");                              //157
  resultList.push_back("HealthRecord/PT/hrec_10_158place.pnml");                              //158
  resultList.push_back("ShieldPPPs/PT/shield_s_ppp_005_a_158place.pnml");                     //158
  resultList.push_back("ShieldPPPt/PT/shield_t_ppp_002_b_159place.pnml");                     //159
  resultList.push_back("HealthRecord/PT/hrec_11_159place.pnml");                              //159
  resultList.push_back("HealthRecord/PT/hrec_12_160place.pnml");                              //160
  resultList.push_back("HealthRecord/PT/hrec_13_161place.pnml");                              //161
  resultList.push_back("HealthRecord/PT/hrec_14_162place.pnml");                              //162
  resultList.push_back("HealthRecord/PT/hrec_15_163place.pnml");                              //163
  resultList.push_back("ShieldRVs/PT/shield_s_rv_004_b_163place.pnml");                       //163
  resultList.push_back("GPUForwardProgress/PT/gpufp_40_a_168place.pnml");                     //168
  resultList.push_back("DiscoveryGPU/PT/discovery_06_b_184place.pnml");                       //184
  resultList.push_back("GPUForwardProgress/PT/gpufp_08_b_188place.pnml");                     //188
  resultList.push_back("ShieldRVt/PT/shield_t_rv_004_b_203place.pnml");                       //203
  resultList.push_back("ShieldRVs/PT/shield_s_rv_005_b_203place.pnml");                       //203
  resultList.push_back("DiscoveryGPU/PT/discovery_07_b_212place.pnml");                       //212
  resultList.push_back("ShieldIIPt/PT/shield_t_iip_003_b_213place.pnml");                     //213

  // XB worst-case graphs
  //resultList.push_back("xb_slow100.pnml");
  //resultList.push_back("xb_slow200.pnml");
  /*resultList.push_back("xb_slow300.pnml");
  resultList.push_back("xb_slow400.pnml");
  resultList.push_back("xb_slow500.pnml");
  resultList.push_back("xb_slow600.pnml");*/

  return resultList;
}

//Main experimentation function
//Runs each algorithm on a list of graphs from PNML files with varying preprocessing amounts
//Prints the results and writes them to a csv-file
void experiment(std::list<std::string> pathStrings, int minPreprocess, int maxPreprocess,
                bool useInitialMarking, std::list<algorithmType> runTypes, std::string fileName) {
  //The amount of files and algorithms to run experiments on - is used to init the size of the csv-file rows
  int noFiles = pathStrings.size();
  int noAlgorithms = runTypes.size();

  //CSV filename and empty container for the rows and init row 0 headers
  std::vector<std::vector<std::string>> grid = initCsvGrid(noFiles, noAlgorithms);
  //The current csv row to insert results into
  int csvRow = 0;

  if(minPreprocess < 0) {
        minPreprocess = 0;
  }
  if(maxPreprocess < minPreprocess) {
    minPreprocess = maxPreprocess;
  }    
  if(maxPreprocess < 0){
      grid[0].insert(grid[0].end(), {"Nodes" , "SCCs","Algorithm type", "Running time (ms)", "Symbolic steps"});

  } else if(maxPreprocess == 0) {
    grid[0].insert(grid[0].end(), {"Nodes", "SCCs", "Algorithm type", "Running time (ms)", "Symbolic steps" });

  }

  //Read all the files, create their graphs and run the algorithms on them
  for(std::string pathString : pathStrings) {
    //std::cout << "###### Running experiment on file at path: " << pathString << std::endl;
    //Create the graph from the PNML-file
    Graph graph = parseFileToGraph2(pathString);
    //Graph graph = PNMLtoGraph(pathString, useInitialMarking); //THIS IS NORMAL LINE

    //Write number of places and relations to csv-file
    std::string noOfPlaces = std::to_string(graph.cube.size());
    std::string noOfRelations = std::to_string(graph.relations.size());
    int i = 1;
    for(algorithmType algo : runTypes) {
      grid[csvRow+i].insert(grid[csvRow+i].end(), {pathString, noOfPlaces, noOfRelations});
      i++;
    }
    std::cout << ";" << noOfRelations;
    grid = preprocessAndRun(graph, maxPreprocess, minPreprocess, runTypes, grid, csvRow);

    //Move down in the csv grid to make way for running all algorithms on next graph
    csvRow = csvRow+noAlgorithms;
  }
  int totalSteps = 0;
  int totalTime = 0;
  for(int i = 1; i < grid.size()-1; i++ ){
    totalSteps = totalSteps + stoi(grid[i][7]);
    totalTime = totalTime + stoi(grid[i][6]);
  }
  //std::cout << "---------------------------------------------" << std::endl;
  //std::cout << "Total steps: " << totalSteps << ", total time: " << totalTime << std::endl;
  grid[grid.size()-1].insert(grid[grid.size()-1].end(), {"Total", "", "", "", "", "", std::to_string(totalTime), std::to_string(totalSteps) });

  writeToCSV(fileName, grid);
}

//Run all algorithms with all pruning steps that are powers of 2 between max and min
//maxPruning < 0 means fixed-point pruning
std::vector<std::vector<std::string>> preprocessAndRun(const Graph &graph, int maxPruning, int minPruning,
                                                       std::list<algorithmType> runTypes,
                                                       std::vector<std::vector<std::string>> grid, int row) {
  if(maxPruning < 0) {
    //std::cout << "### With pre-processing (fixed point)" << std::endl;
    Graph processedGraph = graphPreprocessingFixedPoint(graph);


    //std::cout << "Counting with SatCount..:" << std::endl;
    double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
    //std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

    std::string nodeCountString =  std::to_string(nodeCount);
    std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

    for(int i = 1 ; i <= runTypes.size() ; i++) {
      grid[row+i].push_back(nodeCountString);
    }

    grid = timeAll(processedGraph, runTypes, grid, row);
    //std::cout << std::endl;
  }
  else {
    if(maxPruning == 0) {
      //std::cout << "### With no pre-processing" << std::endl;
      Graph processedGraph = graphPreprocessing(graph, 0);

      //std::cout << "Counting with SatCount..:" << std::endl;
      double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
      //std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

      std::string nodeCountString =  std::to_string(nodeCount);
      std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

      std::cout << ";" << nodeCount;

      for(int i = 1 ; i <= runTypes.size() ; i++) {
        grid[row+i].push_back(nodeCountString);
      }

      grid = timeAll(graph, runTypes, grid, row);
    }
    else {
      //std::cout << "### With pre-processing (" << std::to_string(maxPruning) << " or fixed-point)" << std::endl;
      std::pair<Graph, int> result = graphPreprocessingFixedPointWithMax(graph, maxPruning);
      Graph processedGraph = result.first;

      //std::cout << "Counting with SatCount..:" << std::endl;
      double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
      //std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

      std::string nodeCountString =  std::to_string(nodeCount);
      std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

      for(int i = 1 ; i <= runTypes.size() ; i++) {
        grid[row+i].push_back(nodeCountString);
      }

      int newMax = result.second;
      int newMax2Pow = pow(2,floor(log2(newMax-1)));

      grid = timeAll(processedGraph, runTypes, grid, row);
      //std::cout << std::endl;
      grid[row].insert(grid[row].end(), {"Nodes", "SCC's", "Algorithm type", std::to_string(newMax) + " pruning steps (ms)", "Symbolic steps" });

      for(int i = newMax2Pow; i >= minPruning; i = floor(i/2)) {
        //std::cout << "### With pre-processing (" << std::to_string(i) << ")" << std::endl;
        processedGraph = graphPreprocessing(graph, i);

        //std::cout << "Counting with SatCount..:" << std::endl;
        double nodeCount = processedGraph.nodes.SatCount(processedGraph.cube);
        //std::cout << "Graph size: " << std::to_string(nodeCount) << " nodes" << std::endl;

        std::string nodeCountString =  std::to_string(nodeCount);
        std::replace(nodeCountString.begin(), nodeCountString.end(), '.', ',');

        for(int i = 1 ; i <= runTypes.size() ; i++) {
          grid[row+i].push_back(nodeCountString);
        }

        grid = timeAll(processedGraph, runTypes, grid, row);
        //std::cout << std::endl;

        grid[row].insert(grid[row].end(), {"Nodes", "SCC's","Algorithm type", std::to_string(i) + " pruning steps runtime (ms)", "Symbolic steps" });

        if(i == 0 || i == minPruning) {
          break;
        }
      }
      row = row + runTypes.size();
    }
  }
  return grid;
}

//Finds SCCs on a graph with each algorithm, and appends them to the CSV-grid which is returned
std::vector<std::vector<std::string>> timeAll(const Graph &graph, std::list<algorithmType> runTypes, std::vector<std::vector<std::string>> grid, int row) {
  int i = 1;
  for(algorithmType runType : runTypes) {
    //std::cout << "Running algorithm: " << algoToString(runType) << std::endl;
    std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> runResults = timeRun(graph, runType);
    std::list<sylvan::Bdd> sccList = std::get<0>(runResults);
    std::chrono::duration<long, std::milli> duration = std::get<1>(runResults);

    grid[row+i].insert(grid[row+i].end(), {std::to_string(sccList.size()), algoToString(runType), std::to_string(duration.count()), std::to_string(std::get<2>(runResults))});

    i++;
  }
  return grid;
}

//Runs the specified algorithm on the graph and returns how long it took and the number of symbolic steps
//Also prints timing and results
std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> timeRun(const Graph &graph, algorithmType runType) {
  SccResult sccAndSteps;
  std::list<sylvan::Bdd> sccList;
  int steps = 0;
  auto start = std::chrono::high_resolution_clock::now();
  switch(runType) {
    case lockstepSat:
      sccAndSteps = lockstepSaturation(graph);
      break;
    case lockstepRelUnion:
      sccAndSteps = lockstepRelationUnion(graph);
      break;
    case xbSat:
      sccAndSteps = xieBeerel<Saturation>(graph);
      break;
    case xbRelUnion:
      sccAndSteps = xieBeerel<RelationUnion>(graph);
      break;
    case skeleton:
      sccAndSteps = skeletonAlg(graph);
      break;
    case chain:
      sccAndSteps = chainAlg(graph);
      break;
    case xbRelUnionBottom:
      sccAndSteps = xieBeerelBottom<RelationUnion>(graph);
      break;
    case xbSatBottom:
      sccAndSteps = xieBeerelBottom<Saturation>(graph);
      break;
    case chainBottomAdvanced:
      sccAndSteps = chainAlgBottomAdvanced(graph);
      break;
    case chainBottomSpecialFWD:
      sccAndSteps = chainAlgBottomSpecialFWD(graph);
      break;
    case chainBottomSingleRec:
      sccAndSteps = chainAlgBottomSingleRecCall(graph);
      break;
    case chainBottomSingleRecSpecialFWD:
      sccAndSteps = chainAlgBottomSingleRecSpecialFWD(graph);
      break;
    case chainBottomSingleRecForwardLoop:
      sccAndSteps = chainAlgBottomSingleRecForwardLoop(graph);
      break;
    case chainBottomForwardLoop:
      sccAndSteps = chainAlgBottomForwardLoop(graph);
      break;
    case chainBottomSingleRecCumulative:
      sccAndSteps = chainAlgBottomSingleRecCallCumulative(graph);
      break;
    case chainBottomSingleRecExtra:
      sccAndSteps = chainAlgBottomSingleRecCallExtra(graph);
      break;
    case chainBottomSingleRecSwitch:
      sccAndSteps = chainAlgBottomSingleRecCallSwitch(graph);
      break;
    case chainBottomSingleRecSwitchAndBasin:
      sccAndSteps = chainAlgBottomSingleRecCallSwitchAndBasin(graph);
      break;
    case chainBottomApproxPick:
      sccAndSteps = chainAlgBottomApproxPick(graph);
      break;
    case xbBottomApproxPick:
      sccAndSteps = xbAlgBottomApproxPick(graph);
      break;
    case chainBottomSingleRecInitState:
      sccAndSteps = chainAlgBottomSingleRecCallInitState(graph);
      break;
    case xbBottomInitState:
      sccAndSteps = xieBeerelBottomInitState<RelationUnion>(graph);
      break;
  }

  auto stop = std::chrono::high_resolution_clock::now();
  std::chrono::duration<long, std::milli> duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
  sccList = sccAndSteps.sccs;
  steps = sccAndSteps.symbolicSteps;

  std::cout << ";" << sccList.size() << ";" << duration.count() << ";" << steps << std::endl;

  // std::cout << "Time elapsed (" << algoToString(runType) << "): " << duration.count() << " milliseconds" << std::endl;
  // std::cout << "Found " << sccList.size() << " SCCs" << std::endl;
  // std::cout << "Used " << steps << " symbolic steps" << std::endl << std::endl;
  std::tuple<std::list<sylvan::Bdd>, std::chrono::duration<long, std::milli>, int> result = {sccList, duration, steps};
  return result;
}

////////////////////////////////////////////////////////////////////////////////
// CSV
////////////////////////////////////////////////////////////////////////////////


//Writes the grid to a file at fileName.csv
void writeToCSV(std::string fileName, std::vector<std::vector<std::string>> grid) {
  std::ofstream myFile;
  std::string csvFile = fileName + ".csv";
  myFile.open(csvFile);

  //Takes semi-colon separated cells row by row and writes to .csv file
  for(std::vector<std::string> row : grid) {
    for(std::string cell : row) {
      myFile << cell + ";";
    }
    myFile << "\n";

  }
  myFile.close();
}

//Initializes an empty csv grid with the appropriate amount of rows to insert into
std::vector<std::vector<std::string>> initCsvGrid(int noOfExperimentGraphs, int noOfAlgorithms) {
  int noOfRows = (noOfExperimentGraphs) * (noOfAlgorithms) + 2;
  std::vector<std::vector<std::string>> grid(noOfRows, std::vector<std::string>(0));
  grid[0].insert(grid[0].end(), {"File", "Places", "Relations"});
  return grid;
}

////////////////////////////////////////////////////////////////////////////////
//Pre-processing
////////////////////////////////////////////////////////////////////////////////

//Sorts the relations by their top and prunes the graph pruningSteps times
Graph graphPreprocessing(const Graph &graph, int pruningSteps) {
  Graph resultGraph = graph;
  resultGraph = sortRelations(resultGraph);

  for(int i = 0; i < pruningSteps; i++) {
    resultGraph = pruneGraph(resultGraph);
  }

  double prunedNodes = differenceBdd(graph.nodes, resultGraph.nodes).SatCount(graph.cube);
  if(prunedNodes > 0) {
    // std::cout << "Pruned " << std::to_string(prunedNodes) << " nodes" << std::endl;
    // std::cout << "Finished pre-processing of graph" << std::endl;
  }
  return resultGraph;
}

//Sorts the relations by their top and prunes the graph until it has no more 1-node SCCs
Graph graphPreprocessingFixedPoint(const Graph &graph) {
  Graph resultGraph = graph;
  resultGraph = sortRelations(resultGraph);

  resultGraph = fixedPointPruning(resultGraph);

  double prunedNodes = differenceBdd(graph.nodes, resultGraph.nodes).SatCount(graph.cube);
  // std::cout << "Pruned " << std::to_string(prunedNodes) << " nodes" << std::endl;
  // std::cout << "Finished pre-processing of graph" << std::endl;
  return resultGraph;
}

//Sorts the relations by their top and prunes the graph until it has no more 1-node SCCs or
//it has used the maximum number of pruning steps
std::pair<Graph, int> graphPreprocessingFixedPointWithMax(const Graph &graph, int maxPruning) {
  Graph resultGraph = graph;
  resultGraph = sortRelations(resultGraph);

  std::pair<Graph, int> result = fixedPointPruningWithMax(resultGraph, maxPruning);

  double prunedNodes = differenceBdd(graph.nodes, resultGraph.nodes).SatCount(graph.cube);
  // std::cout << "Pruned " << std::to_string(prunedNodes) << " nodes" << std::endl;
  // std::cout << "Finished pre-processing of graph" << std::endl;
  return result;
}

////////////////////////////////////////////////////////////////////////////////
//SCC list verification
////////////////////////////////////////////////////////////////////////////////
//For an SCC-list, check that it does not have duplicates, that no SCCs overlap,
//and that it covers the entire original graph
void validateAlgoSccResults(const std::list<sylvan::Bdd> resultSccList, const Graph originalGraph) {
  bool hasDuplicates = containsDuplicateSccs(resultSccList);
  if(hasDuplicates) {
    // std::cout << "Lockstep saturation gave two or more equal SCCs" << std::endl;
  }
  bool hasOverlap = sccListContainsDifferentSccsWithDuplicateNodes(resultSccList);
  if(hasOverlap) {
    // std::cout << "Lockstep saturation gave overlapping SCCs" << std::endl;
  }
  bool foundAllSCCs = sccUnionIsWholeBdd(resultSccList, originalGraph.nodes);
  if(!foundAllSCCs) {
    // std::cout << "Lockstep saturation did not find SCCs covering all nodes" << std::endl;
  }
}

//Finds whether an SCC is contained in a list of SCCs
bool sccListContains(sylvan::Bdd target, std::list<sylvan::Bdd> sccList) {
  for(sylvan::Bdd scc : sccList) {
    if(scc == target) {
      return true;
    }
  }
  return false;
}

//Checks for duplicates in a list of SCCs
bool containsDuplicateSccs(const std::list<sylvan::Bdd> sccList) {
  for(sylvan::Bdd scc1 : sccList) {
    int duplicates = 0;
    for(sylvan::Bdd scc2 : sccList) {
      if(scc1 == scc2) {
        duplicates++;
      }
    }
    if(duplicates > 1) {
      return true;
    }
  }
  return false;
}

//Checks that no SCCs in an SCC list overlap
bool sccListContainsDifferentSccsWithDuplicateNodes(const std::list<sylvan::Bdd> sccList) {
  for(sylvan::Bdd scc1 : sccList) {
    for(sylvan::Bdd scc2 : sccList) {
      sylvan::Bdd intersect = intersectBdd(scc1, scc2);
      if(intersect != leaf_false() && scc1 != scc2) {
        return true;
      }
    }
  }
  return false;
}

//Checks that an SCC list covers a whole nodeset
bool sccUnionIsWholeBdd(const std::list<sylvan::Bdd> sccList, const sylvan::Bdd nodes) {
  sylvan::Bdd bddUnion = leaf_false();
  for(sylvan::Bdd scc : sccList) {
    bddUnion = unionBdd(bddUnion, scc);
  }
  sylvan::Bdd result = differenceBdd(nodes, bddUnion);
  return result == leaf_false();
}

//Checks that two SCC lists contain the same SCCs
bool sccListCorrectness(const std::list<sylvan::Bdd> sccList1, const std::list<sylvan::Bdd> sccList2) {
  if(sccList1.size() != sccList2.size()) {
    // std::cout << "The size of the scc lists were different" << std::endl;
    return false;
  }
  if(containsDuplicateSccs(sccList1) || containsDuplicateSccs(sccList2)) {
    // std::cout << "One of the lists contained duplicate sccs" << std::endl;
    return false;
  }
  for(sylvan::Bdd scc : sccList1) {
    if(!sccListContains(scc, sccList2)) {
      // std::cout << "The lists didn't contain the same scc" << std::endl;
      return false;
    }
  }
  return true;
}

void analyzeRelations(std::deque<Relation> relations) {
  std::list<std::list<bool>> matrix = {};

  std::vector<std::vector<bool>> grid(relations.size(), std::vector<bool>(relations.size()));
  for (int i = 0; i < relations.size(); i++) {
      for (int j = 0; j < relations.size(); j++) {
          Relation relationi = relations[i];
          Relation relationj = relations[j];
          if(i == j) {
              grid[i][j] = false;
              continue;
            }
          //Top is smallest variable and bottom is largest
          if((relationi.bottom >= relationj.top && relationi.bottom <= relationj.bottom)
              || (relationi.top >= relationj.top && relationi.top <= relationj.bottom)
              || (relationj.top >= relationi.top && relationj.top <= relationi.bottom)
              || (relationj.bottom >= relationi.top && relationj.bottom <= relationi.bottom)) {
            grid[i][j] = true;
          } else {
            grid[i][j] = false;
          }
      }
  }
  //calculate average out-degree:
  double matrixsum = 0;
  for (int i = 0; i < relations.size(); i++) {
    for (int j = 0; j < relations.size(); j++) {
      matrixsum += grid[i][j];
    }
  }
  double avgMatrixSum = matrixsum / relations.size();
  double normOutDegree = avgMatrixSum / relations.size();
  double normEdges = avgMatrixSum / 2;
  double density = matrixsum / (relations.size() * (relations.size()-1));
  //printVectorGrid(grid);
  std::cout << "Normalized out-degree: " << normOutDegree << std::endl;
  std::cout << "Normalized number of edges: " << normEdges << std::endl;
  std::cout << "|V|: " << relations.size() << std::endl;
  std::cout << "|E|: " << matrixsum/2 << std::endl;
  std::cout << "Density: " << density << std::endl;
}

void printVectorGrid(std::vector<std::vector<bool>> grid){
  for(std::vector<bool> vec : grid) {
    for(bool b : vec) {
      if(b) {
        std::cout << " 1";
      } else  {
        std::cout << " 0";
      }
    }
    std::cout<< std::endl;
  }
}

void analyzeAllRelations(std::list<std::string> pnmlList) {
  for(std::string pnml : pnmlList ){
    Graph graph = PNMLtoGraph(pnml, true);
    analyzeRelations(graph.relations);
    std::cout << std::endl;
  }
}