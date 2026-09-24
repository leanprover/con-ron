import ConRon.Bridge.Grouping.Core6

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

#keeps_ind allLevelParamsDefinedGo 2
#keeps allLevelParamsDefined
#keeps_ind constsResolveFGo 2
#keeps constsResolveFFast unresolvedConstsError installValue checkValueGroup

end ConRon.Bridge.Grouping
