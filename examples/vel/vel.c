#include <math.h>

double get_current_velocity(void);
double get_current_braking_force(void);
double get_current_accel_force(void);
void throw_velocity_exception(void);

const double maxVehicleVelocityAllowed = 58.1152; //58.1152m/s = 130 mph
const double vehicleMass = 1000; //in kg
const double timeStep = .001; //1 ms
/**
 * A function to calculate the new velocity displayed
 * This function returns
 * -1 : If there is an error, such as if the velocity is
 *        beyond the maximum allowed velocity
**/

int updateDisplayVelocity(void)
{
  double currentV = get_current_velocity();
  double brakeF = get_current_braking_force(); //in N
  double accelF = get_current_accel_force(); // in N
  double newV = 0.0;
  
  int displayV = 0; 

  newV = currentV + (((accelF - brakeF)/vehicleMass)*timeStep);
  
  if (newV > maxVehicleVelocityAllowed) //check to make sure that we are not above limit
  {
    throw_velocity_exception();
    return (-1); //-1 meaning error
  } 
  
  displayV = newV;
  return (displayV);
}

