import BealMatveevBealV25B0Search.ChunkGroups.Group090
import BealMatveevBealV25B0Search.ChunkGroups.Group091
import BealMatveevBealV25B0Search.ChunkGroups.Group092
import BealMatveevBealV25B0Search.ChunkGroups.Group093
import BealMatveevBealV25B0Search.ChunkGroups.Group094
import BealMatveevBealV25B0Search.ChunkGroups.Group095
import BealMatveevBealV25B0Search.ChunkGroups.Group096
import BealMatveevBealV25B0Search.ChunkGroups.Group097
import BealMatveevBealV25B0Search.ChunkGroups.Group098
import BealMatveevBealV25B0Search.ChunkGroups.Group099

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_09 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 9 + 10 * g + i))
      (500 * (100 * 9 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_090 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_091 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_092 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_093 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_094 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_095 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_096 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_097 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_098 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_099 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
