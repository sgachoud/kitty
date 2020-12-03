/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <iostream>
#include <fstream>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "isop.hpp"

namespace kitty
{
  constexpr char PROBLEM_FILE[] = "threshold_identification_ilp.lp";
  constexpr char SOLUTION_FILE[] = "threshold_identification_sol.txt";
  
  typedef std::vector<std::vector<uint8_t>> ConstraintVector;

void print_lp( ConstraintVector const& gts, ConstraintVector const& lts,
              uint8_t num_vars, std::ostream& os = std::cout )
{
  /* the objective function */
  os << "min:";
  for ( uint8_t i( 0 ); i < num_vars; ++i )
  {
    os << " + w" << int(i);
  }
  os << " + T;" << std::endl;

  /* the constraints */
  for ( std::vector<uint8_t> const& gt : gts )
  {
    if( gt.empty() ) os << "1 ";
    for ( uint8_t v : gt )
    {
      os << "+ w" << int(v) << " ";
    }
    os << ">= T;" << std::endl;
  }
  
  for ( std::vector<uint8_t> const& lt : lts )
  {
    if( lt.empty() ) os << "0 ";
    for ( uint8_t v : lt )
    {
      os << "+ w" << int(v) << " ";
    }
    os << "<= T -1;" << std::endl;
  }

  for ( uint8_t i( 0 ); i < num_vars; ++i )
  {
    os << "+ w" << int(i) << " >= 0;"<< std::endl;
  }
  os << "+ T >= 0;" << std::endl;
  
  /* variable type declaration */
  os << "integer ";
  for ( uint8_t i( 0 ); i < num_vars; ++i )
  {
    os << " w" << int(i) << ",";
  }
  os << " T;" << std::endl;
}

void dump_lp( ConstraintVector const& gts, ConstraintVector const& lts,
              uint8_t num_vars )
{
  std::ofstream fout( PROBLEM_FILE, std::ofstream::out );
  print_lp( gts, lts, num_vars, fout );
  fout.close();
}

void solve_ILP()
{
  const std::string directive( "lp_solve " + std::string(PROBLEM_FILE) + " > " + std::string(SOLUTION_FILE) );
  std::system(directive.c_str());
}

void read_solution( std::vector<int64_t>& sol, uint8_t num_vars )
{
  std::ifstream fin( std::string(SOLUTION_FILE), std::ifstream::in );
  if ( !fin.is_open() )
  {
    std::cerr << "[e] Error opening the solution file (is_threshold)." << std::endl;
    return;
  }

  /* parsing */
  std::string line, obj;
  std::getline( fin, line ); /* first line is empty */
  if( !line.empty() ) return; /* if not empty then infeasible */
  std::getline( fin, obj ); /* second line is the value of objective function */
  std::getline( fin, line ); /* third line is empty */
  std::getline( fin, line ); /* fourth line is useless */
  
  sol.resize( num_vars + 1 );
  
  while ( std::getline( fin, line ) )
  {
    std::string var_name, value = "";
    std::stringstream ss( line );
    std::getline( ss, var_name, ' ' );
    while ( value.size() == 0u && std::getline( ss, value, ' ' ) ) { }
    
    int int_value = std::stoi(value);
    switch( var_name[0])
    {
      case 'w':
      {
        uint8_t var_id = std::stoi(var_name.erase( 0, 1 ));
        sol[var_id] = int_value;
        break;
      }
      case 'T':
      {
        sol[num_vars] = int_value;
        break;
      }
      default:
        break;
    }
  }
}

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  TT ctt = tt;
  std::vector<bool> inverted( ctt.num_vars() );
  
  if( !positive_unateness( ctt, inverted ) ) return false;
  
  ConstraintVector gts;
  ConstraintVector lts;
  
  fillConstraints( ctt, gts, lts );
  
  dump_lp( gts, lts, ctt.num_vars() );
  
  solve_ILP();
  
  read_solution( linear_form, ctt.num_vars() );
  
  if( linear_form.empty() ) return false;

  for( uint8_t i( 0 ); i < ctt.num_vars(); i++ )
  {
    if( inverted[i] )
    {
      linear_form[i] *= -1;
      linear_form[ctt.num_vars()] += linear_form[i];
    }
  }
  
  /* if tt is TF: */
  /* push the weight and threshold values into `linear_form` */
  if ( plf )
  {
    *plf = linear_form;
  }
  return true;
}

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
void fillConstraints( const TT& tt, ConstraintVector& gts, ConstraintVector& lts )
{
  
  std::vector<cube> on_set( isop( tt ) );
  std::vector<cube> off_set( isop(~tt) );
  
  for( cube c : on_set)
  {
    std::vector<uint8_t> vars;
    for( uint8_t i( 0 ); i < tt.num_vars(); i++ )
    {
      if( c.get_mask( i ) && c.get_bit( i )) vars.emplace_back( i );
      //if( c.get_mask( i ) ) vars.emplace_back( i );
    }
    gts.emplace_back( vars );
  }
  
  for( cube c : off_set)
  {
    std::vector<uint8_t> vars;
    for( uint8_t i( 0 ); i < tt.num_vars(); i++ )
    {
      if( !c.get_mask( i ) || ( c.get_mask( i ) && c.get_bit( i ) ) ) vars.emplace_back( i );
      //if( !c.get_mask( i ) ) vars.emplace_back( i );
    }
    lts.emplace_back( vars );
  }
}

/*!
  \brief Check whether the truth table is unate and ensure its positivity.
  
  Given a truth table this function check whether it is unate in all its
  variables and ensure the positivity of the unateness by inverting inplace
  variables in which the truth table is negative unate. The content of the
  truth table is not guaranteed to be in its original form this function 
  returns `false`.
   
  \param tt the truth table
  \return `true` if `tt` is unate in all its variables, `false` otherwise.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool positive_unateness( TT& tt, std::vector<bool>& inverted )
{
  for( uint32_t i( 0 ); i < tt.num_vars(); i++ )
  {
    bool inv;
    if( !positive_unateness( tt, i, inv ) ) return false;
    inverted[i] = inv;
  }
  return true;
}

/*!
  \brief Check whether the truth table is unate in the specified variable 
  and ensure its positivity.
  
  Given a truth table this function check whether it is unate in the specified
  variable its and ensure the positivity of the unateness by inverting inplace
  the variable if the truth table is negative unate in it.
   
  \param tt the truth table
  \param var the variable it is wishable apply this function
  \return `true` if `tt` is unate in `var`, `false` otherwise.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool positive_unateness( TT& tt, uint8_t var, bool& inverted )
{
  const auto cof0 = cofactor0( tt, var );
  const auto cof1 = cofactor1( tt, var );
  
  if( binary_predicate( cof1, cof0, std::greater_equal<>() ) ) 
  {
    inverted = false;
    return true;
  }
  if( binary_predicate( cof1, cof0, std::less_equal<>() ) )
  {
    flip_inplace( tt, var );
    inverted = true;
    return true;
  }
  return false;
}


} /* namespace kitty */
