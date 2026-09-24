import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0400
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0401
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0402
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0403
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0404
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0405
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0406
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0407
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0408
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0409

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_040 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 40 + i)) (500 * (10 * 40 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0400
  by_cases h1 : i = 1
  · subst i
    exact chunk_0401
  by_cases h2 : i = 2
  · subst i
    exact chunk_0402
  by_cases h3 : i = 3
  · subst i
    exact chunk_0403
  by_cases h4 : i = 4
  · subst i
    exact chunk_0404
  by_cases h5 : i = 5
  · subst i
    exact chunk_0405
  by_cases h6 : i = 6
  · subst i
    exact chunk_0406
  by_cases h7 : i = 7
  · subst i
    exact chunk_0407
  by_cases h8 : i = 8
  · subst i
    exact chunk_0408
  by_cases h9 : i = 9
  · subst i
    exact chunk_0409
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
