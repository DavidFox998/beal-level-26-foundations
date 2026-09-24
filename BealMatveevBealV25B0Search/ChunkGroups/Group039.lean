import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0390
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0391
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0392
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0393
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0394
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0395
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0396
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0397
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0398
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0399

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_039 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 39 + i)) (500 * (10 * 39 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0390
  by_cases h1 : i = 1
  · subst i
    exact chunk_0391
  by_cases h2 : i = 2
  · subst i
    exact chunk_0392
  by_cases h3 : i = 3
  · subst i
    exact chunk_0393
  by_cases h4 : i = 4
  · subst i
    exact chunk_0394
  by_cases h5 : i = 5
  · subst i
    exact chunk_0395
  by_cases h6 : i = 6
  · subst i
    exact chunk_0396
  by_cases h7 : i = 7
  · subst i
    exact chunk_0397
  by_cases h8 : i = 8
  · subst i
    exact chunk_0398
  by_cases h9 : i = 9
  · subst i
    exact chunk_0399
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
