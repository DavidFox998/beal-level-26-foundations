import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0150
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0151
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0152
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0153
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0154
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0155
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0156
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0157
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0158
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0159

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_015 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 15 + i)) (500 * (10 * 15 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0150
  by_cases h1 : i = 1
  · subst i
    exact chunk_0151
  by_cases h2 : i = 2
  · subst i
    exact chunk_0152
  by_cases h3 : i = 3
  · subst i
    exact chunk_0153
  by_cases h4 : i = 4
  · subst i
    exact chunk_0154
  by_cases h5 : i = 5
  · subst i
    exact chunk_0155
  by_cases h6 : i = 6
  · subst i
    exact chunk_0156
  by_cases h7 : i = 7
  · subst i
    exact chunk_0157
  by_cases h8 : i = 8
  · subst i
    exact chunk_0158
  by_cases h9 : i = 9
  · subst i
    exact chunk_0159
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
