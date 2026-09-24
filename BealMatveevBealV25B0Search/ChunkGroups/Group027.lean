import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0270
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0271
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0272
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0273
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0274
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0275
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0276
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0277
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0278
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0279

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_027 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 27 + i)) (500 * (10 * 27 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0270
  by_cases h1 : i = 1
  · subst i
    exact chunk_0271
  by_cases h2 : i = 2
  · subst i
    exact chunk_0272
  by_cases h3 : i = 3
  · subst i
    exact chunk_0273
  by_cases h4 : i = 4
  · subst i
    exact chunk_0274
  by_cases h5 : i = 5
  · subst i
    exact chunk_0275
  by_cases h6 : i = 6
  · subst i
    exact chunk_0276
  by_cases h7 : i = 7
  · subst i
    exact chunk_0277
  by_cases h8 : i = 8
  · subst i
    exact chunk_0278
  by_cases h9 : i = 9
  · subst i
    exact chunk_0279
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
