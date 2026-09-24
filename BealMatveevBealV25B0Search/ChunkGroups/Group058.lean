import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0580
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0581
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0582
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0583
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0584
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0585
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0586
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0587
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0588
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0589

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_058 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 58 + i)) (500 * (10 * 58 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0580
  by_cases h1 : i = 1
  · subst i
    exact chunk_0581
  by_cases h2 : i = 2
  · subst i
    exact chunk_0582
  by_cases h3 : i = 3
  · subst i
    exact chunk_0583
  by_cases h4 : i = 4
  · subst i
    exact chunk_0584
  by_cases h5 : i = 5
  · subst i
    exact chunk_0585
  by_cases h6 : i = 6
  · subst i
    exact chunk_0586
  by_cases h7 : i = 7
  · subst i
    exact chunk_0587
  by_cases h8 : i = 8
  · subst i
    exact chunk_0588
  by_cases h9 : i = 9
  · subst i
    exact chunk_0589
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
