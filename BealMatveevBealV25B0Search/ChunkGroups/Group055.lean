import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0550
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0551
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0552
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0553
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0554
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0555
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0556
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0557
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0558
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0559

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_055 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 55 + i)) (500 * (10 * 55 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0550
  by_cases h1 : i = 1
  · subst i
    exact chunk_0551
  by_cases h2 : i = 2
  · subst i
    exact chunk_0552
  by_cases h3 : i = 3
  · subst i
    exact chunk_0553
  by_cases h4 : i = 4
  · subst i
    exact chunk_0554
  by_cases h5 : i = 5
  · subst i
    exact chunk_0555
  by_cases h6 : i = 6
  · subst i
    exact chunk_0556
  by_cases h7 : i = 7
  · subst i
    exact chunk_0557
  by_cases h8 : i = 8
  · subst i
    exact chunk_0558
  by_cases h9 : i = 9
  · subst i
    exact chunk_0559
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
