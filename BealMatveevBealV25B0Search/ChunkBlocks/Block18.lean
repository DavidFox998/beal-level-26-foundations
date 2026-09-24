import BealMatveevBealV25B0Search.ChunkGroups.Group180
import BealMatveevBealV25B0Search.ChunkGroups.Group181
import BealMatveevBealV25B0Search.ChunkGroups.Group182
import BealMatveevBealV25B0Search.ChunkGroups.Group183
import BealMatveevBealV25B0Search.ChunkGroups.Group184
import BealMatveevBealV25B0Search.ChunkGroups.Group185
import BealMatveevBealV25B0Search.ChunkGroups.Group186
import BealMatveevBealV25B0Search.ChunkGroups.Group187
import BealMatveevBealV25B0Search.ChunkGroups.Group188
import BealMatveevBealV25B0Search.ChunkGroups.Group189

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_18 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 18 + 10 * g + i))
      (500 * (100 * 18 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_180 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_181 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_182 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_183 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_184 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_185 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_186 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_187 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_188 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_189 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
