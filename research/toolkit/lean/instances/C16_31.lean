import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 31 of the cap-16 certificate: slots 31744 .. 32767 -/
theorem chk_31 : chunkCheck 16 T stdSt 31744 1024 = true := by decide +kernel

end Row16
