import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0410
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0411
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0412
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0413
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0414
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0415
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0416
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0417
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0418
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0419

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_041 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 41 + i)) (500 * (10 * 41 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0410
  by_cases h1 : i = 1
  · subst i
    exact chunk_0411
  by_cases h2 : i = 2
  · subst i
    exact chunk_0412
  by_cases h3 : i = 3
  · subst i
    exact chunk_0413
  by_cases h4 : i = 4
  · subst i
    exact chunk_0414
  by_cases h5 : i = 5
  · subst i
    exact chunk_0415
  by_cases h6 : i = 6
  · subst i
    exact chunk_0416
  by_cases h7 : i = 7
  · subst i
    exact chunk_0417
  by_cases h8 : i = 8
  · subst i
    exact chunk_0418
  by_cases h9 : i = 9
  · subst i
    exact chunk_0419
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
