import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0160
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0161
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0162
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0163
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0164
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0165
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0166
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0167
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0168
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0169

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_016 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 16 + i)) (500 * (10 * 16 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0160
  by_cases h1 : i = 1
  · subst i
    exact chunk_0161
  by_cases h2 : i = 2
  · subst i
    exact chunk_0162
  by_cases h3 : i = 3
  · subst i
    exact chunk_0163
  by_cases h4 : i = 4
  · subst i
    exact chunk_0164
  by_cases h5 : i = 5
  · subst i
    exact chunk_0165
  by_cases h6 : i = 6
  · subst i
    exact chunk_0166
  by_cases h7 : i = 7
  · subst i
    exact chunk_0167
  by_cases h8 : i = 8
  · subst i
    exact chunk_0168
  by_cases h9 : i = 9
  · subst i
    exact chunk_0169
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
