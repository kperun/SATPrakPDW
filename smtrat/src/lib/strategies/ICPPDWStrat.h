/**
 * @file ICPPDWStrat.h
 */
#pragma once

#include "../solver/Manager.h"

#include "../modules/ICPPDWModule/ICPPDWModule.h"
#include "../modules/SATModule/SATModule.h"
#include "../modules/CADModule/CADModule.h"

namespace smtrat
{
    /**
     * Strategy description.
     *
     * @author
     * @since
     * @version
     *
     */
    class ICPPDWStrat: public Manager
    {
        public:
            ICPPDWStrat(): Manager() {
				setStrategy({
					addBackend<SATModule<SATSettings1>>({
						addBackend<ICPPDWModule<ICPPDWSettingsDebug>>({
                            addBackend<CADModule<CADSettingsSplitPath>>()
                        })
					})
				});
			}
    };

}    // namespace smtrat
