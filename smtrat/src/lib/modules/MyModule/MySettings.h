/**
 * @file MySettings.h
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
 *
 * @version 2017-04-17
 * Created on 2017-04-17.
 */

#pragma once

namespace smtrat
{
	struct MySettings1
	{
		/// Name of the Module
		static constexpr auto moduleName = "MyModule<MySettings1>";
		/**
		 * Example for a setting.
		 */
		static const bool example_setting = true;
	};
}
