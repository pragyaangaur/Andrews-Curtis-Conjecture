import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 242 of the cap-16 certificate: slots 247808 .. 248831 -/
theorem chk_242 : chunkCheck 16 T stdSt 247808 1024 = true := by decide +kernel

end Row16
