#pragma once

#include "ICPContractionCandidate.h"


 namespace smtrat
 {

  template<typename Settings>
  class ICPContractionCandidate;
  double ICPContractionCandidate<Settings>::getWeight();





  template<typename Settings>
  class CompareCandidates{
    public:
    bool operator()(ICPContractionCandidate<Settings>* cc1,ICPContractionCandidate<Settings>* cc2){
      if(cc1->getWeight()>cc2->getWeight()){
        return cc1;
      }else{
        return cc2;
      }
    }
  };



 }