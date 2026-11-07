import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 74 of the cap-16 certificate: slots 75776 .. 76799 -/
theorem chk_74 : chunkCheck 16 T stdSt 75776 1024 = true := by decide +kernel

end Row16
