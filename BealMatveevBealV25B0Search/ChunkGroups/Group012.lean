import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0120
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0121
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0122
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0123
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0124
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0125
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0126
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0127
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0128
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0129

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_012 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 12 + i)) (500 * (10 * 12 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0120
  by_cases h1 : i = 1
  · subst i
    exact chunk_0121
  by_cases h2 : i = 2
  · subst i
    exact chunk_0122
  by_cases h3 : i = 3
  · subst i
    exact chunk_0123
  by_cases h4 : i = 4
  · subst i
    exact chunk_0124
  by_cases h5 : i = 5
  · subst i
    exact chunk_0125
  by_cases h6 : i = 6
  · subst i
    exact chunk_0126
  by_cases h7 : i = 7
  · subst i
    exact chunk_0127
  by_cases h8 : i = 8
  · subst i
    exact chunk_0128
  by_cases h9 : i = 9
  · subst i
    exact chunk_0129
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
