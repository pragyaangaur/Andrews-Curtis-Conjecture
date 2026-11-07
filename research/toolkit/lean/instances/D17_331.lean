import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 331 of the cap-17 certificate: slots 169472 .. 169983 -/
theorem chk_331 : chunkCheck 17 T stdSt 169472 512 = true := by decide +kernel

end Row17
