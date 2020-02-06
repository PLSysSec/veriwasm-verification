#include <fenv.h>
#include <stdio.h>

typedef union {
  double f;
  unsigned long long l;
} mytype;

double rawToDouble(unsigned long long l)
{
  mytype m;
  m.l = l;
  return (m.f);
}

int updateDisplayVelocity(void);

double get_current_velocity(void)
{
  //return (58.0);
  return (rawToDouble(0x402BBFFFFFFFFFFF));

}

double get_current_braking_force(void)
{
  //return (59000000.0);
  return (rawToDouble(0x41FBFE12ADB01C80));
  //return (0);
}

double get_current_accel_force(void)
{
  //return (0.0);
  return (rawToDouble(0x41F401137808fcd4));
}

void throw_velocity_exception(void)
{
  printf("** VELOCITY EXCEPTION **\n");
}

int main(void)
{
  printf("ROUNDING_MODE (0?)     = %d\n", fegetround());
  printf("CURRENT_VEL            = %f m/s\n", get_current_velocity());
  printf("CURRENT_BREAKING_FORCE = %f N\n", get_current_braking_force());
  printf("CURRENT_ACCEL_FORCE    = %f N\n", get_current_accel_force());
  printf("DISPLAY_VEL            = %d m/s\n", updateDisplayVelocity());

 return (0);
}

