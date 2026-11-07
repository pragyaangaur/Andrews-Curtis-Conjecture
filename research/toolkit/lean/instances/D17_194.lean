import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 194 of the cap-17 certificate: slots 99328 .. 99839 -/
theorem chk_194 : chunkCheck 17 T stdSt 99328 512 = true := by decide +kernel

end Row17
