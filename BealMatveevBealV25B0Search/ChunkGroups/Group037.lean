import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0370
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0371
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0372
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0373
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0374
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0375
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0376
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0377
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0378
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0379

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_037 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 37 + i)) (500 * (10 * 37 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0370
  by_cases h1 : i = 1
  · subst i
    exact chunk_0371
  by_cases h2 : i = 2
  · subst i
    exact chunk_0372
  by_cases h3 : i = 3
  · subst i
    exact chunk_0373
  by_cases h4 : i = 4
  · subst i
    exact chunk_0374
  by_cases h5 : i = 5
  · subst i
    exact chunk_0375
  by_cases h6 : i = 6
  · subst i
    exact chunk_0376
  by_cases h7 : i = 7
  · subst i
    exact chunk_0377
  by_cases h8 : i = 8
  · subst i
    exact chunk_0378
  by_cases h9 : i = 9
  · subst i
    exact chunk_0379
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
