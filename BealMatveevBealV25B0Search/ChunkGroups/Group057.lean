import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0570
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0571
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0572
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0573
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0574
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0575
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0576
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0577
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0578
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0579

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_057 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 57 + i)) (500 * (10 * 57 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0570
  by_cases h1 : i = 1
  · subst i
    exact chunk_0571
  by_cases h2 : i = 2
  · subst i
    exact chunk_0572
  by_cases h3 : i = 3
  · subst i
    exact chunk_0573
  by_cases h4 : i = 4
  · subst i
    exact chunk_0574
  by_cases h5 : i = 5
  · subst i
    exact chunk_0575
  by_cases h6 : i = 6
  · subst i
    exact chunk_0576
  by_cases h7 : i = 7
  · subst i
    exact chunk_0577
  by_cases h8 : i = 8
  · subst i
    exact chunk_0578
  by_cases h9 : i = 9
  · subst i
    exact chunk_0579
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
