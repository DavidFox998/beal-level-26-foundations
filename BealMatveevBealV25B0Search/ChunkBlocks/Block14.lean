import BealMatveevBealV25B0Search.ChunkGroups.Group140
import BealMatveevBealV25B0Search.ChunkGroups.Group141
import BealMatveevBealV25B0Search.ChunkGroups.Group142
import BealMatveevBealV25B0Search.ChunkGroups.Group143
import BealMatveevBealV25B0Search.ChunkGroups.Group144
import BealMatveevBealV25B0Search.ChunkGroups.Group145
import BealMatveevBealV25B0Search.ChunkGroups.Group146
import BealMatveevBealV25B0Search.ChunkGroups.Group147
import BealMatveevBealV25B0Search.ChunkGroups.Group148
import BealMatveevBealV25B0Search.ChunkGroups.Group149

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_14 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 14 + 10 * g + i))
      (500 * (100 * 14 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_140 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_141 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_142 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_143 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_144 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_145 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_146 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_147 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_148 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_149 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
