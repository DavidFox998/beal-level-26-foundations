import BealMatveevBealV25B0Search.ChunkGroups.Group120
import BealMatveevBealV25B0Search.ChunkGroups.Group121
import BealMatveevBealV25B0Search.ChunkGroups.Group122
import BealMatveevBealV25B0Search.ChunkGroups.Group123
import BealMatveevBealV25B0Search.ChunkGroups.Group124
import BealMatveevBealV25B0Search.ChunkGroups.Group125
import BealMatveevBealV25B0Search.ChunkGroups.Group126
import BealMatveevBealV25B0Search.ChunkGroups.Group127
import BealMatveevBealV25B0Search.ChunkGroups.Group128
import BealMatveevBealV25B0Search.ChunkGroups.Group129

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_12 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 12 + 10 * g + i))
      (500 * (100 * 12 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_120 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_121 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_122 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_123 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_124 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_125 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_126 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_127 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_128 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_129 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
