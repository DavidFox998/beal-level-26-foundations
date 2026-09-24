import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0180
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0181
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0182
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0183
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0184
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0185
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0186
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0187
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0188
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0189

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_018 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 18 + i)) (500 * (10 * 18 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0180
  by_cases h1 : i = 1
  · subst i
    exact chunk_0181
  by_cases h2 : i = 2
  · subst i
    exact chunk_0182
  by_cases h3 : i = 3
  · subst i
    exact chunk_0183
  by_cases h4 : i = 4
  · subst i
    exact chunk_0184
  by_cases h5 : i = 5
  · subst i
    exact chunk_0185
  by_cases h6 : i = 6
  · subst i
    exact chunk_0186
  by_cases h7 : i = 7
  · subst i
    exact chunk_0187
  by_cases h8 : i = 8
  · subst i
    exact chunk_0188
  by_cases h9 : i = 9
  · subst i
    exact chunk_0189
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
