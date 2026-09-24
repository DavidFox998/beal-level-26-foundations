import BealMatveevBealV25B0Search.ChunkGroups.Group030
import BealMatveevBealV25B0Search.ChunkGroups.Group031
import BealMatveevBealV25B0Search.ChunkGroups.Group032
import BealMatveevBealV25B0Search.ChunkGroups.Group033
import BealMatveevBealV25B0Search.ChunkGroups.Group034
import BealMatveevBealV25B0Search.ChunkGroups.Group035
import BealMatveevBealV25B0Search.ChunkGroups.Group036
import BealMatveevBealV25B0Search.ChunkGroups.Group037
import BealMatveevBealV25B0Search.ChunkGroups.Group038
import BealMatveevBealV25B0Search.ChunkGroups.Group039

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_03 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 3 + 10 * g + i))
      (500 * (100 * 3 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_030 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_031 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_032 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_033 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_034 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_035 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_036 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_037 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_038 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_039 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
