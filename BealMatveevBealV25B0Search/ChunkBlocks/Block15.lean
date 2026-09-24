import BealMatveevBealV25B0Search.ChunkGroups.Group150
import BealMatveevBealV25B0Search.ChunkGroups.Group151
import BealMatveevBealV25B0Search.ChunkGroups.Group152
import BealMatveevBealV25B0Search.ChunkGroups.Group153
import BealMatveevBealV25B0Search.ChunkGroups.Group154
import BealMatveevBealV25B0Search.ChunkGroups.Group155
import BealMatveevBealV25B0Search.ChunkGroups.Group156
import BealMatveevBealV25B0Search.ChunkGroups.Group157
import BealMatveevBealV25B0Search.ChunkGroups.Group158
import BealMatveevBealV25B0Search.ChunkGroups.Group159

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_15 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 15 + 10 * g + i))
      (500 * (100 * 15 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_150 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_151 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_152 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_153 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_154 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_155 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_156 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_157 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_158 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_159 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
