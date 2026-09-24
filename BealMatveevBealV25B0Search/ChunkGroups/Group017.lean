import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0170
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0171
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0172
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0173
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0174
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0175
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0176
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0177
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0178
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0179

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_017 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 17 + i)) (500 * (10 * 17 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0170
  by_cases h1 : i = 1
  · subst i
    exact chunk_0171
  by_cases h2 : i = 2
  · subst i
    exact chunk_0172
  by_cases h3 : i = 3
  · subst i
    exact chunk_0173
  by_cases h4 : i = 4
  · subst i
    exact chunk_0174
  by_cases h5 : i = 5
  · subst i
    exact chunk_0175
  by_cases h6 : i = 6
  · subst i
    exact chunk_0176
  by_cases h7 : i = 7
  · subst i
    exact chunk_0177
  by_cases h8 : i = 8
  · subst i
    exact chunk_0178
  by_cases h9 : i = 9
  · subst i
    exact chunk_0179
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
