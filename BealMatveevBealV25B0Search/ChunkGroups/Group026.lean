import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0260
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0261
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0262
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0263
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0264
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0265
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0266
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0267
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0268
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0269

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_026 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 26 + i)) (500 * (10 * 26 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0260
  by_cases h1 : i = 1
  · subst i
    exact chunk_0261
  by_cases h2 : i = 2
  · subst i
    exact chunk_0262
  by_cases h3 : i = 3
  · subst i
    exact chunk_0263
  by_cases h4 : i = 4
  · subst i
    exact chunk_0264
  by_cases h5 : i = 5
  · subst i
    exact chunk_0265
  by_cases h6 : i = 6
  · subst i
    exact chunk_0266
  by_cases h7 : i = 7
  · subst i
    exact chunk_0267
  by_cases h8 : i = 8
  · subst i
    exact chunk_0268
  by_cases h9 : i = 9
  · subst i
    exact chunk_0269
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
