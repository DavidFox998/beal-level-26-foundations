import BealMatveevBealV25B0Search.ChunkGroups.Group100
import BealMatveevBealV25B0Search.ChunkGroups.Group101
import BealMatveevBealV25B0Search.ChunkGroups.Group102
import BealMatveevBealV25B0Search.ChunkGroups.Group103
import BealMatveevBealV25B0Search.ChunkGroups.Group104
import BealMatveevBealV25B0Search.ChunkGroups.Group105
import BealMatveevBealV25B0Search.ChunkGroups.Group106
import BealMatveevBealV25B0Search.ChunkGroups.Group107
import BealMatveevBealV25B0Search.ChunkGroups.Group108
import BealMatveevBealV25B0Search.ChunkGroups.Group109

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_10 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 10 + 10 * g + i))
      (500 * (100 * 10 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_100 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_101 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_102 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_103 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_104 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_105 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_106 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_107 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_108 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_109 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
