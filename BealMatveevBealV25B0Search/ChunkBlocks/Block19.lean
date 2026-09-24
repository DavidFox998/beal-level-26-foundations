import BealMatveevBealV25B0Search.ChunkGroups.Group190
import BealMatveevBealV25B0Search.ChunkGroups.Group191
import BealMatveevBealV25B0Search.ChunkGroups.Group192
import BealMatveevBealV25B0Search.ChunkGroups.Group193
import BealMatveevBealV25B0Search.ChunkGroups.Group194
import BealMatveevBealV25B0Search.ChunkGroups.Group195
import BealMatveevBealV25B0Search.ChunkGroups.Group196
import BealMatveevBealV25B0Search.ChunkGroups.Group197
import BealMatveevBealV25B0Search.ChunkGroups.Group198
import BealMatveevBealV25B0Search.ChunkGroups.Group199

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- One hundred independent 500-value certificates. -/
theorem block_19 (g i : ℕ) (hg : g < 10) (hi : i < 10) :
    checkRange (500 * (100 * 19 + 10 * g + i))
      (500 * (100 * 19 + 10 * g + i + 1)) = true := by
  by_cases h0 : g = 0
  · subst g
    exact group_190 i hi
  by_cases h1 : g = 1
  · subst g
    exact group_191 i hi
  by_cases h2 : g = 2
  · subst g
    exact group_192 i hi
  by_cases h3 : g = 3
  · subst g
    exact group_193 i hi
  by_cases h4 : g = 4
  · subst g
    exact group_194 i hi
  by_cases h5 : g = 5
  · subst g
    exact group_195 i hi
  by_cases h6 : g = 6
  · subst g
    exact group_196 i hi
  by_cases h7 : g = 7
  · subst g
    exact group_197 i hi
  by_cases h8 : g = 8
  · subst g
    exact group_198 i hi
  by_cases h9 : g = 9
  · subst g
    exact group_199 i hi
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
