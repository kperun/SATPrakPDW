#pragma once

#include "ICPContractionCandidate.h"


 namespace smtrat
 {

  template<typename Settings>
  class ICPContractionCandidate;






  template<typename Settings>
  class CompareCandidates{
    public:
    bool operator()(ICPContractionCandidate<Settings>* cc1,ICPContractionCandidate<Settings>* cc2){
      if(cc1->getWeight() < cc2->getWeight()){
        return true;
      }else{
        return false;
      }
    }
  };



 }
