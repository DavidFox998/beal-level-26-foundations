import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0450
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0451
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0452
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0453
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0454
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0455
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0456
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0457
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0458
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0459

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_045 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 45 + i)) (500 * (10 * 45 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0450
  by_cases h1 : i = 1
  · subst i
    exact chunk_0451
  by_cases h2 : i = 2
  · subst i
    exact chunk_0452
  by_cases h3 : i = 3
  · subst i
    exact chunk_0453
  by_cases h4 : i = 4
  · subst i
    exact chunk_0454
  by_cases h5 : i = 5
  · subst i
    exact chunk_0455
  by_cases h6 : i = 6
  · subst i
    exact chunk_0456
  by_cases h7 : i = 7
  · subst i
    exact chunk_0457
  by_cases h8 : i = 8
  · subst i
    exact chunk_0458
  by_cases h9 : i = 9
  · subst i
    exact chunk_0459
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
